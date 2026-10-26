#!/usr/bin/env python3
"""Tests for the Lean JSON parser and printer.

Two parts.

1. JSONTestSuite (https://github.com/nst/JSONTestSuite), if a clone
   is found. The harness reads the path from the environment
   variable JSONTESTSUITE_DIR, or looks next to this repository.
   For each file in test_parsing: y_* files must be accepted, and
   the canonical reprint must parse again to the same canonical
   text; n_* files must be rejected; i_* files are skipped and
   counted, because the suite marks them as behaviour a reader may
   choose. If no clone is found, this part records that in the
   results file instead of failing.

2. A differential run against Python's `json` module, with a
   recorded seed. Random values are built in Python with numbers
   held as source text inside the RFC 8259 grammar, strings with
   escapes and non-ASCII characters, nested arrays and objects.
   Each value is printed in the canonical form the Lean printer
   uses, and also in a whitespace-varied form, and the Lean answer
   for both must be the canonical form. Random text mutations must
   then be accepted or rejected alike by both sides, with two
   named differences:

   - Python accepts `NaN`, `Infinity` and `-Infinity`. The oracle
     is set to reject them, because RFC 8259 does not allow them,
     and the generator never feeds them as valid input.
   - Python accepts lone surrogate escapes such as `\\ud800` and
     holds the surrogate as a character. The Lean parser rejects
     them, because a Lean character is one Unicode scalar value.
     Mutations where Python accepts and the parsed value holds a
     surrogate are counted as this difference, not as failures,
     and the Lean side must reject them.

   Malformed request lines, in the shape of the codec harness,
   must be answered `error`.

    python3 tests/run_tests.py [--seed N] [--count N]

The tool is driven the way the codec harness drives its tool: one
batch process per chunk of requests, input written and closed,
output drained until the process exits. It builds the executable
first, writes tests/TEST-RESULTS.md, and exits non-zero if any
check fails. It needs Python 3.11 or later.
"""

import argparse
import json
import os
import random
import subprocess
import sys
import threading
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
EXE = ROOT / ".lake" / "build" / "bin" / "json"
RESULTS = ROOT / "tests" / "TEST-RESULTS.md"
TIMEOUT = 900
BUILD_TIMEOUT = 3600
CHUNK = 2000

SEED_DEFAULT = 20261025


def codes(text):
    return ",".join(str(ord(c)) for c in text)


def request(text):
    return "parse " + codes(text)


def run_tool(lines, timeout=TIMEOUT):
    """Run the tool on a batch of request lines.

    Returns (answers, problem). No right answer is longer than its
    request plus a small constant, so output past twice the input
    plus 64 bytes a line is stopped, not read until memory runs
    out.
    """
    data = "".join(line + "\n" for line in lines)
    raw = data.encode("utf-8")
    limit = 2 * len(raw) + 64 * (len(lines) + 1)
    try:
        proc = subprocess.Popen(
            [str(EXE)],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
    except OSError as e:
        return [], f"could not run {EXE}: {e.strerror or e}"
    out, err = bytearray(), bytearray()

    def feed():
        try:
            proc.stdin.write(raw)
            proc.stdin.close()
        except (BrokenPipeError, ValueError):
            pass

    def drain(stream, buf, cap):
        while chunk := stream.read1(1 << 16):
            buf += chunk
            if len(buf) > cap:
                proc.kill()
                return

    threads = [
        threading.Thread(target=feed),
        threading.Thread(target=drain, args=(proc.stdout, out, limit)),
        threading.Thread(target=drain, args=(proc.stderr, err, 1 << 20)),
    ]
    for t in threads:
        t.start()
    problem = None
    try:
        proc.wait(timeout=timeout)
    except subprocess.TimeoutExpired:
        proc.kill()
        problem = f"no end after {timeout} seconds"
    for t in threads:
        t.join()
    proc.wait()
    if len(out) > limit:
        problem = problem or f"more than {limit} bytes of output, stopped"
    elif proc.returncode != 0 and not problem:
        tail = " / ".join(
            bytes(err).decode("utf-8", "backslashreplace").splitlines()[-3:]
        )
        problem = f"exit status {proc.returncode}: {tail}"
    text = bytes(out).decode("utf-8", "backslashreplace")
    if text and not text.endswith("\n"):
        problem = problem or "the last answer has no LF"
    answers = text.split("\n")
    if answers and answers[-1] == "":
        answers.pop()
    if len(answers) != len(lines) and not problem:
        problem = f"tool gave {len(answers)} answers for {len(lines)} requests"
    return answers, problem


def ask_all(lines):
    """Chunked run_tool. Answers align with lines, or None entries."""
    answers = []
    problems = []
    for i in range(0, len(lines), CHUNK):
        chunk = lines[i : i + CHUNK]
        ans, problem = run_tool(chunk)
        if problem:
            problems.append(problem)
            ans = ans + [None] * (len(chunk) - len(ans))
        answers += ans
    return answers, problems


def answer_codes(answer):
    """The character codes of an `ok:` answer, or None."""
    if not isinstance(answer, str) or not answer.startswith("ok:"):
        return None
    rest = answer[3:]
    if rest == "":
        return []
    return [int(x) for x in rest.split(",")]


def answer_text(answer):
    cs = answer_codes(answer)
    if cs is None:
        return None
    return "".join(chr(c) for c in cs)


# ---------------------------------------------------------------- the
# Python mirror of the Lean printer.


class Num:
    """A JSON number held as source text, as the Lean value holds it."""

    def __init__(self, text):
        self.text = text


def escape_str(s):
    out = ['"']
    for c in s:
        n = ord(c)
        if c == '"':
            out.append('\\"')
        elif c == "\\":
            out.append("\\\\")
        elif n == 8:
            out.append("\\b")
        elif n == 9:
            out.append("\\t")
        elif n == 10:
            out.append("\\n")
        elif n == 12:
            out.append("\\f")
        elif n == 13:
            out.append("\\r")
        elif n < 0x20:
            out.append("\\u%04x" % n)
        else:
            out.append(c)
    out.append('"')
    return "".join(out)


def canonical(v):
    if v is None:
        return "null"
    if v is True:
        return "true"
    if v is False:
        return "false"
    if isinstance(v, Num):
        return v.text
    if isinstance(v, str):
        return escape_str(v)
    if isinstance(v, list):
        return "[" + ",".join(canonical(x) for x in v) + "]"
    if isinstance(v, tuple):  # one object: a list of (key, value) pairs
        return "{" + ",".join(
            escape_str(k) + ":" + canonical(x) for k, x in v
        ) + "}"
    raise TypeError(repr(v))


# ---------------------------------------------------------------- the
# strict Python oracle.


def _reject_constant(name):
    raise ValueError("constant not allowed: " + name)


def oracle_loads(text):
    return json.loads(text, parse_constant=_reject_constant)


def has_surrogate(v):
    if isinstance(v, str):
        return any(0xD800 <= ord(c) <= 0xDFFF for c in v)
    if isinstance(v, list):
        return any(has_surrogate(x) for x in v)
    if isinstance(v, dict):
        return any(has_surrogate(k) or has_surrogate(x) for k, x in v.items())
    return False


# ---------------------------------------------------------------- the
# random values.

STRING_CHARS = (
    "abz AZ09 \t\n\r\"\\/{}[],:"
    "éüßαλ"
    "😀🎉𝄞"
    "́à"
    "\x00\x01\x07\x08\x0b\x0c\x1f\x7f"
)


def rand_string(rng):
    n = rng.randrange(0, 10)
    return "".join(rng.choice(STRING_CHARS) for _ in range(n))


def rand_number(rng):
    out = []
    if rng.random() < 0.3:
        out.append("-")
    if rng.random() < 0.3:
        out.append("0")
    else:
        out.append(rng.choice("123456789"))
        for _ in range(rng.randrange(0, 4)):
            out.append(rng.choice("0123456789"))
    if rng.random() < 0.4:
        out.append(".")
        for _ in range(rng.randrange(1, 4)):
            out.append(rng.choice("0123456789"))
    if rng.random() < 0.3:
        out.append(rng.choice("eE"))
        if rng.random() < 0.5:
            out.append(rng.choice("+-"))
        for _ in range(rng.randrange(1, 3)):
            out.append(rng.choice("0123456789"))
    return Num("".join(out))


def rand_value(rng, depth):
    choices = ["null", "bool", "num", "str"]
    if depth < 5:
        choices += ["arr", "arr", "obj"]
    kind = rng.choice(choices)
    if kind == "null":
        return None
    if kind == "bool":
        return rng.random() < 0.5
    if kind == "num":
        return rand_number(rng)
    if kind == "str":
        return rand_string(rng)
    if kind == "arr":
        return [rand_value(rng, depth + 1) for _ in range(rng.randrange(0, 5))]
    pairs = []
    for _ in range(rng.randrange(0, 5)):
        pairs.append((rand_string(rng), rand_value(rng, depth + 1)))
    return tuple(pairs)


def with_whitespace(rng, v):
    """The same value printed with random legal whitespace."""
    if isinstance(v, list):
        inner = ("," + rng.choice(["", " ", "\n", " \t"])).join(
            with_whitespace(rng, x) for x in v
        )
        return (
            "[" + rng.choice(["", " ", "\n"]) + inner
            + rng.choice(["", " ", "\r\n"]) + "]"
        )
    if isinstance(v, tuple):
        inner = ("," + rng.choice(["", " ", "\n"])).join(
            escape_str(k) + rng.choice(["", " "]) + ":" + rng.choice(["", " ", "\t"])
            + with_whitespace(rng, x)
            for k, x in v
        )
        return "{" + rng.choice(["", " "]) + inner + rng.choice(["", " "]) + "}"
    return canonical(v)


MUTATE_CHARS = "0123456789.eE+-\"\\/,[]{}: truefalsn\x00\x1f\x7fé"


def mutate(rng, text):
    chars = list(text)
    for _ in range(rng.randrange(1, 4)):
        if not chars:
            break
        op = rng.choice(["replace", "insert", "delete", "truncate"])
        pos = rng.randrange(0, len(chars))
        if op == "replace":
            chars[pos] = rng.choice(MUTATE_CHARS)
        elif op == "insert":
            chars.insert(pos, rng.choice(MUTATE_CHARS))
        elif op == "delete":
            del chars[pos]
        else:
            chars = chars[:pos]
    return "".join(chars)


# ---------------------------------------------------------------- the
# parts of the run.


def run_suite():
    """Returns (lines, failures) for the results file."""
    lines = []
    failures = []
    suite_dir = os.environ.get("JSONTESTSUITE_DIR")
    candidates = []
    if suite_dir:
        candidates.append(Path(suite_dir))
    candidates.append(ROOT.parent / "JSONTestSuite")
    candidates.append(ROOT / "JSONTestSuite")
    found = None
    for cand in candidates:
        if (cand / "test_parsing").is_dir():
            found = cand
            break
    if found is None:
        lines.append(
            "JSONTestSuite: not run. No clone found (set JSONTESTSUITE_DIR "
            "to a clone of https://github.com/nst/JSONTestSuite)."
        )
        return lines, failures
    lines.append("JSONTestSuite: clone found, test_parsing used")
    parsing = sorted((found / "test_parsing").glob("*.json"))
    y_files = [p for p in parsing if p.name.startswith("y_")]
    n_files = [p for p in parsing if p.name.startswith("n_")]
    i_files = [p for p in parsing if p.name.startswith("i_")]

    jobs = []
    meta = []  # ("y"|"n", name) per job, plus ("skip-encoding", name) aside
    for path in y_files:
        try:
            text = path.read_bytes().decode("utf-8")
        except UnicodeDecodeError:
            failures.append(f"suite y {path.name}: file is not valid UTF-8")
            meta.append(("y-bad", path.name))
            jobs.append(None)
            continue
        meta.append(("y", path.name))
        jobs.append(request(text))
    n_encoding = 0
    for path in n_files:
        try:
            text = path.read_bytes().decode("utf-8")
        except UnicodeDecodeError:
            # The bytes are not UTF-8, so no JSON text over Unicode
            # scalar values can be formed from them: counted as
            # rejected at the encoding level, and named in the
            # results.
            n_encoding += 1
            meta.append(("n-encoding", path.name))
            jobs.append(None)
            continue
        meta.append(("n", path.name))
        jobs.append(request(text))
    real_jobs = [j for j in jobs if j is not None]
    answers, problems = ask_all(real_jobs)
    for problem in problems:
        failures.append(f"suite: tool problem: {problem}")
    answer_iter = iter(answers)
    per_job = {}
    for idx, job in enumerate(jobs):
        if job is not None:
            per_job[idx] = next(answer_iter)
    reprint_jobs = []
    reprint_idx = []
    for idx, (kind, name) in enumerate(meta):
        if kind != "y":
            continue
        reprint = answer_text(per_job.get(idx))
        if reprint is None:
            failures.append(f"suite y {name}: rejected, answer {per_job.get(idx)!r}")
        else:
            reprint_jobs.append(request(reprint))
            reprint_idx.append((idx, reprint))
    answers2, problems2 = ask_all(reprint_jobs)
    for problem in problems2:
        failures.append(f"suite reprint: tool problem: {problem}")
    y_ok = 0
    for (idx, reprint), ans2 in zip(reprint_idx, answers2):
        name = meta[idx][1]
        if answer_text(ans2) == reprint:
            y_ok += 1
        else:
            failures.append(
                f"suite y {name}: reprint not stable: {reprint!r} then {ans2!r}"
            )
    n_ok = n_encoding
    for idx, (kind, name) in enumerate(meta):
        if kind != "n":
            continue
        if per_job.get(idx) == "none":
            n_ok += 1
        else:
            failures.append(f"suite n {name}: accepted, answer {per_job.get(idx)!r}")
    lines.append(
        f"JSONTestSuite y_ files accepted with a stable reprint: "
        f"{y_ok} of {len(y_files)}"
    )
    lines.append(f"JSONTestSuite n_ files rejected: {n_ok} of {len(n_files)}")
    if n_encoding:
        lines.append(
            "JSONTestSuite n_ files rejected at the encoding level "
            f"(bytes not valid UTF-8): {n_encoding}"
        )
    lines.append(f"JSONTestSuite i_ files skipped: {len(i_files)}")
    return lines, failures


MALFORMED = [
    "",
    "pars 1,2",
    "parse 1,,2",
    "parse 1,2,",
    "parse -1",
    "parse 12a",
    "parse 1 2",
    "parse 55296",  # a surrogate code point: not a Unicode scalar value
    "parse 1114112",  # past U+10FFFF
    "parse 999999999999999999999999999999",  # overlong decimal guard
    "Parse 91,93",
    "parse 91;93",
]


def run_differential(seed, count):
    lines = []
    failures = []
    rng = random.Random(seed)
    inputs = 0
    agreements = 0
    # 1. generated values: canonical and whitespace-varied texts
    jobs = []
    expected = []
    for _ in range(count):
        v = rand_value(rng, 0)
        want = canonical(v)
        jobs.append(request(want))
        expected.append(want)
        varied = (
            rng.choice(["", " ", "\n\t"])
            + with_whitespace(rng, v)
            + rng.choice(["", " ", "\r"])
        )
        jobs.append(request(varied))
        expected.append(want)
    answers, problems = ask_all(jobs)
    for problem in problems:
        failures.append(f"differential values: tool problem: {problem}")
    for job, want, ans in zip(jobs, expected, answers):
        inputs += 1
        if answer_text(ans) == want:
            agreements += 1
        else:
            failures.append(f"value {job[:80]}: want ok {want!r}, got {ans!r}")
    # 2. mutations compared against the strict oracle
    diff_surrogate = 0
    mut_inputs = 0
    mut_agree = 0
    texts = [mutate(rng, canonical(rand_value(rng, 0))) for _ in range(count)]
    answers, problems = ask_all([request(t) for t in texts])
    for problem in problems:
        failures.append(f"differential mutations: tool problem: {problem}")
    for text, ans in zip(texts, answers):
        mut_inputs += 1
        try:
            oracle = oracle_loads(text)
            oracle_ok = True
        except Exception:
            oracle = None
            oracle_ok = False
        lean_ok = answer_codes(ans) is not None
        if oracle_ok and has_surrogate(oracle):
            if lean_ok:
                failures.append(
                    f"mutation {text!r}: lone surrogate accepted by lean: {ans!r}"
                )
            else:
                diff_surrogate += 1
                mut_agree += 1
            continue
        if oracle_ok != lean_ok:
            failures.append(
                f"mutation {text!r}: oracle_ok={oracle_ok}, lean answer {ans!r}"
            )
            continue
        if oracle_ok:
            reprint = answer_text(ans)
            try:
                again = oracle_loads(reprint)
            except Exception:
                failures.append(
                    f"mutation {text!r}: lean reprint {reprint!r} "
                    "not readable by oracle"
                )
                continue
            if again != oracle:
                failures.append(
                    f"mutation {text!r}: values differ: oracle {oracle!r}, "
                    f"lean reprint {reprint!r}"
                )
                continue
        mut_agree += 1
    inputs += mut_inputs
    agreements += mut_agree
    # Fixed lone surrogate cases: random mutations rarely build one,
    # so the named difference is also exercised directly. Python
    # accepts every one of these; the Lean parser must reject all.
    surrogate_texts = [
        '"\\ud800"',
        '"\\udc00"',
        '"\\ud800abc"',
        '"a\\udc00b"',
        '["\\ud83d"]',
        '"\\ud800\\u0041"',  # high surrogate, then a non-low escape
        '"\\ud800x"',  # high surrogate, then no escape at all
    ]
    answers, problems = ask_all([request(t) for t in surrogate_texts])
    for problem in problems:
        failures.append(f"surrogate cases: tool problem: {problem}")
    for text, ans in zip(surrogate_texts, answers):
        inputs += 1
        try:
            oracle = oracle_loads(text)
            oracle_ok = True
        except Exception:
            oracle_ok = False
        if not (oracle_ok and has_surrogate(oracle)):
            failures.append(
                f"surrogate case {text!r}: oracle does not accept it as expected"
            )
        elif ans == "none":
            diff_surrogate += 1
            agreements += 1
        else:
            failures.append(
                f"surrogate case {text!r}: lean accepted, answer {ans!r}"
            )
    lines.append(f"Differential inputs: {inputs}")
    lines.append(f"Differential agreements: {agreements}")
    lines.append(
        "Cases where Python accepts a lone surrogate escape and "
        f"Lean rejects it (named difference): {diff_surrogate}"
    )
    # 3. malformed request lines
    bad_ok = 0
    answers, problems = ask_all(MALFORMED)
    for problem in problems:
        failures.append(f"malformed: tool problem: {problem}")
    for line, ans in zip(MALFORMED, answers):
        if ans == "error":
            bad_ok += 1
        else:
            failures.append(f"malformed {line!r}: want error, got {ans!r}")
    lines.append(f"Malformed requests answered error: {bad_ok} of {len(MALFORMED)}")
    # A request with no codes at all is the empty text: rejected as
    # JSON, not malformed.
    empty_ok = 0
    answers, _ = ask_all(["parse", "parse "])
    for ans in answers:
        if ans == "none":
            empty_ok += 1
        else:
            failures.append(f"empty request: want none, got {ans!r}")
    lines.append(f"Requests with no codes answered none: {empty_ok} of 2")
    return lines, failures


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", type=int, default=SEED_DEFAULT)
    ap.add_argument("--count", type=int, default=3000)
    args = ap.parse_args()

    build = subprocess.run(
        ["lake", "build"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=BUILD_TIMEOUT,
    )
    if build.returncode != 0:
        print(build.stdout)
        print(build.stderr)
        print("lake build failed")
        return 1

    all_lines = []
    all_failures = []
    lines, failures = run_suite()
    all_lines += lines
    all_failures += failures
    lines, failures = run_differential(args.seed, args.count)
    all_lines += lines
    all_failures += failures

    lean_version = subprocess.run(
        ["lake", "env", "lean", "--version"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=120,
    ).stdout.strip()

    out = ["# Test results", ""]
    out.append("Written by `tests/run_tests.py`. Rerun it to check these numbers.")
    out.append("")
    out.append(
        f"- Oracle: Python {sys.version.split()[0]} `json` (strict constants)"
    )
    out.append(f"- Lean: {lean_version}")
    out.append(f"- Seed: {args.seed}")
    for line in all_lines:
        out.append(f"- {line}")
    out.append(f"- Failures: {len(all_failures)}")
    for failure in all_failures[:50]:
        out.append(f"- FAILURE: {failure}")
    RESULTS.write_text("\n".join(out) + "\n", encoding="utf-8")
    print("\n".join(out))
    return 0 if not all_failures else 1


if __name__ == "__main__":
    sys.exit(main())

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

3. The number layer (slice 2). A `num` request holds one number
   text. Fixed cases cover the shapes of the RFC 8259 number
   grammar. Random numbers are generated in every shape with a
   second recorded seed; the written exponent stays between -60
   and 60 and a text holds at most 40 digits. The oracle is
   Python's `decimal.Decimal`: a text is first checked against
   a strict grammar pattern (Decimal alone accepts spellings
   the grammar refuses, such as `1.` or a leading `+`), then
   read with Decimal, and the canonical text is computed from
   its tuple: the coefficient's trailing zeros are folded into
   the exponent, a zero value prints as `0`, and the rest
   prints in plain notation with the point placed by the
   exponent, a leading `0` below one, and zero padding past
   the digits. That is the canonical rule stated in SPEC.md,
   computed here independently. Equal-value groups (several
   spellings of one value) must all answer with the one
   canonical text. Grammar rejections must answer `none`.
   Canonical answers are fed back in and must answer with
   themselves. The printing limit is exercised too: a text
   whose plain notation would hold more than 10,000 digits
   must answer `none`, and a text at the limit must print.

   The results file also carries an Axiom check section. The
   harness runs `lake env lean Json/Proofs/Verify.lean`, which
   prints the axioms of the headline theorems with
   `#print axioms`, and writes that output into the section.
   If the run fails or a named theorem is missing from the
   output, the harness records a failure instead.

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
import re
import subprocess
import sys
import threading
from decimal import Decimal
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


def num_request(text):
    return "num " + codes(text)


def run_tool(lines, timeout=TIMEOUT, cap_factor=2):
    """Run the tool on a batch of request lines.

    Returns (answers, problem). No right answer to a `parse`
    request is longer than its request plus a small constant, so
    output past twice the input plus 64 bytes a line is stopped,
    not read until memory runs out. A `num` answer can be much
    longer than its request (an exponent unfolds into zeros),
    so number batches pass a larger cap factor.
    """
    data = "".join(line + "\n" for line in lines)
    raw = data.encode("utf-8")
    limit = cap_factor * len(raw) + 64 * (len(lines) + 1)
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


def ask_all(lines, cap_factor=2):
    """Chunked run_tool. Answers align with lines, or None entries."""
    answers = []
    problems = []
    for i in range(0, len(lines), CHUNK):
        chunk = lines[i : i + CHUNK]
        ans, problem = run_tool(chunk, cap_factor=cap_factor)
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


# ---------------------------------------------------------------- the
# number layer (slice 2).

NUM_SEED = 20261026
NUM_RANDOM = 3000

# The RFC 8259 number grammar, as a pattern. Decimal alone is
# not the oracle for acceptance: it takes spellings the grammar
# refuses.
NUMBER_RE = re.compile(
    r"-?(?:0|[1-9][0-9]*)(?:\.[0-9]+)?(?:[eE][+-]?[0-9]+)?"
)


def canonical_number(text):
    """The canonical text of a number text, or None if the
    grammar refuses it. The value is read with Decimal; the
    canonical text is computed from its tuple by the rule in
    SPEC.md: fold the coefficient's trailing zeros into the
    exponent, print zero as `0`, and print the rest in plain
    notation with the point placed by the exponent."""
    if NUMBER_RE.fullmatch(text) is None:
        return None
    sign, digits, exponent = Decimal(text).as_tuple()
    sig = 0
    for d in digits:
        sig = sig * 10 + d
    if sig == 0:
        return "0"
    while sig % 10 == 0:
        sig //= 10
        exponent += 1
    ds = str(sig)
    if exponent >= 0:
        body = ds + "0" * exponent
    else:
        point = len(ds) + exponent
        if point > 0:
            body = ds[:point] + "." + ds[point:]
        else:
            body = "0." + "0" * (-point) + ds
    return ("-" if sign else "") + body


# Pins for the oracle itself, so a wrong oracle cannot agree
# with a wrong tool unnoticed.
ORACLE_PINS = [
    ("0", "0"),
    ("-0", "0"),
    ("-0.0e5", "0"),
    ("1.50", "1.5"),
    ("1e2", "100"),
    ("1E+2", "100"),
    ("1e-2", "0.01"),
    ("1.5e-3", "0.0015"),
    ("123e-5", "0.00123"),
    ("1.2300e2", "123"),
    ("10", "10"),
    ("0.5", "0.5"),
    ("-2.750", "-2.75"),
    ("9007199254740993", "9007199254740993"),
    ("5e-1", "0.5"),
]

FIXED_NUMBERS = [
    # plain integers
    "0", "1", "9", "10", "42", "123456789", "9007199254740993",
    "123456789012345678901234567890",
    # negative integers
    "-1", "-42", "-123456789",
    # fractions
    "0.5", "0.25", "1.5", "3.14159", "0.001", "123.456",
    "1.50", "2.500", "0.10", "10.0", "100.000",
    # zero spellings, including negative zero
    "-0", "0.0", "-0.0", "0.00", "-0.000", "0e0", "0e5", "0e-5",
    "-0.0e5", "0.0E+10", "-0e-0",
    # exponents, both letters, both signs, leading zeros
    "1e0", "1e1", "1e2", "1E2", "1e+2", "1E+2", "1e-2", "1e02",
    "1e007", "1e-007", "1e000", "5e-1", "2.5e-3", "1.25E2",
    "6.02E+23", "1e21", "1e60", "1e-60", "9.99e60", "9.99e-60",
    # point placement around the digits
    "123e-5", "123e-2", "123e-3", "1234e-2", "1.2300e2", "12e-1",
    "120e-2", "0.000001", "1000000e-6", "7e-7",
    # values whose canonical form keeps inner zeros
    "1.01", "1.0001", "100.001", "1.20e3", "102030405060708090",
]

EQUAL_GROUPS = [
    ["1", "1.0", "1.00", "1e0", "1E0", "10e-1", "0.1e1", "100e-2",
     "1.000e0"],
    ["0", "-0", "0.0", "-0.00", "0e5", "-0.0e-5", "0.000E+10"],
    ["1.5", "1.50", "15e-1", "0.15e1", "1.500", "150e-2"],
    ["-2.75", "-2.750", "-275e-2", "-0.275e1", "-27.5e-1"],
    ["100", "1e2", "10e1", "100.0", "0.1e3", "1000e-1"],
    ["0.001", "1e-3", "0.0010", "10e-4", "0.0001e1"],
    ["123.456", "123456e-3", "1.23456e2", "123.4560", "0.123456e3"],
]

NUM_REJECTIONS = [
    "01", "00", "007", "1.", ".5", "-.5", "1e", "1e+", "1e-",
    "+1", "--1", "-", "", "1.e5", "1e5.5", "1..5", "1.5.5",
    "0x1", "1,5", " 1", "1 ", "1 e5", "NaN", "Infinity",
    "-Infinity", "1a", "a1", "e5", ".", "-.", "1ee5", "1e++5",
    "1e--5", "١٢٣", "１２３",
]

NUM_MALFORMED = [
    "num 1,,2",
    "num 1,2,",
    "num -1",
    "num 12a",
    "num 1 2",
    "num 55296",  # a surrogate code point
    "num 1114112",  # past U+10FFFF
    "Num 49",
    "num 49;50",
    "numx 49",
]


def rand_number_text(rng):
    shape = rng.choice(["int", "frac", "exp", "frac_exp", "zero"])
    if shape == "zero":
        return rng.choice(
            ["0", "-0", "0.0", "0.00e3", "0e-5", "-0.0E+10",
             "0.000", "-0e0", "-0.00e-7"]
        )
    out = []
    if rng.random() < 0.4:
        out.append("-")
    if rng.random() < 0.25:
        out.append("0")
    else:
        out.append(rng.choice("123456789"))
        for _ in range(rng.randrange(0, 12)):
            out.append(rng.choice("0123456789"))
    if shape in ("frac", "frac_exp"):
        out.append(".")
        for _ in range(rng.randrange(1, 15)):
            out.append(rng.choice("0123456789"))
    if shape in ("exp", "frac_exp"):
        e = rng.randrange(-60, 61)
        sign = ""
        if e < 0:
            sign = "-"
        elif rng.random() < 0.5:
            sign = "+"
        edigits = str(abs(e))
        if rng.random() < 0.3:
            edigits = "0" * rng.randrange(1, 3) + edigits
        out.append(rng.choice("eE") + sign + edigits)
    return "".join(out)


def ask_num(texts):
    """Ask the tool `num` requests, with the larger output cap."""
    return ask_all([num_request(t) for t in texts], cap_factor=64)


def run_numbers():
    lines = []
    failures = []
    # The oracle pins check the oracle itself, not the tool.
    for text, want in ORACLE_PINS:
        got = canonical_number(text)
        if got != want:
            failures.append(
                f"oracle pin {text!r}: oracle computed {got!r}, pinned {want!r}"
            )
    # 1. fixed cases
    fixed_ok = 0
    answers, problems = ask_num(FIXED_NUMBERS)
    for problem in problems:
        failures.append(f"number fixed: tool problem: {problem}")
    for text, ans in zip(FIXED_NUMBERS, answers):
        want = canonical_number(text)
        if want is None:
            failures.append(f"number fixed {text!r}: oracle refuses a fixed case")
        elif answer_text(ans) == want:
            fixed_ok += 1
        else:
            failures.append(
                f"number fixed {text!r}: want ok {want!r}, got {ans!r}"
            )
    lines.append(
        f"Number fixed cases: {len(FIXED_NUMBERS)} inputs, "
        f"{fixed_ok} agreements"
    )
    # 2. random numbers in every grammar shape
    rng = random.Random(NUM_SEED)
    texts = [rand_number_text(rng) for _ in range(NUM_RANDOM)]
    rand_ok = 0
    answers, problems = ask_num(texts)
    for problem in problems:
        failures.append(f"number random: tool problem: {problem}")
    canonicals = []
    for text, ans in zip(texts, answers):
        want = canonical_number(text)
        got = answer_text(ans)
        canonicals.append(got)
        if want is not None and got == want:
            rand_ok += 1
        else:
            failures.append(
                f"number random {text!r}: want ok {want!r}, got {ans!r}"
            )
    lines.append(
        f"Number random cases (seed {NUM_SEED}): {len(texts)} inputs, "
        f"{rand_ok} agreements"
    )
    # The stated bounds of the random section.
    lines.append(
        "Number random bounds: written exponent between -60 and 60, "
        "at most 40 digits per text"
    )
    # 3. equal-value groups: every spelling answers one text
    group_ok = 0
    spellings = 0
    for group in EQUAL_GROUPS:
        answers, problems = ask_num(group)
        for problem in problems:
            failures.append(f"number groups: tool problem: {problem}")
        want = canonical_number(group[0])
        good = True
        for text, ans in zip(group, answers):
            spellings += 1
            if answer_text(ans) != want or canonical_number(text) != want:
                good = False
                failures.append(
                    f"number group {group[0]!r}: spelling {text!r} "
                    f"answered {ans!r}, want the one text {want!r}"
                )
        if good:
            group_ok += 1
    lines.append(
        f"Number equal-value groups: {len(EQUAL_GROUPS)} groups, "
        f"{spellings} spellings, {group_ok} groups with one canonical text"
    )
    # 4. rejections through `num`
    rej_ok = 0
    answers, problems = ask_num(NUM_REJECTIONS)
    for problem in problems:
        failures.append(f"number rejections: tool problem: {problem}")
    for text, ans in zip(NUM_REJECTIONS, answers):
        if canonical_number(text) is not None:
            failures.append(
                f"number rejection {text!r}: oracle accepts it, test is wrong"
            )
        elif ans == "none":
            rej_ok += 1
        else:
            failures.append(
                f"number rejection {text!r}: want none, got {ans!r}"
            )
    lines.append(
        f"Number rejections answered none: {rej_ok} of {len(NUM_REJECTIONS)}"
    )
    # 5. canonical answers fed back in must answer themselves
    back = [c for c in canonicals if c is not None]
    back_ok = 0
    answers, problems = ask_num(back)
    for problem in problems:
        failures.append(f"number feedback: tool problem: {problem}")
    for text, ans in zip(back, answers):
        if answer_text(ans) == text:
            back_ok += 1
        else:
            failures.append(
                f"number feedback {text!r}: want itself, got {ans!r}"
            )
    lines.append(
        f"Number canonical texts fed back: {len(back)} inputs, "
        f"{back_ok} agreements"
    )
    # 6. malformed `num` request lines and the no-codes request
    bad_ok = 0
    answers, problems = ask_all(NUM_MALFORMED)
    for problem in problems:
        failures.append(f"number malformed: tool problem: {problem}")
    for line, ans in zip(NUM_MALFORMED, answers):
        if ans == "error":
            bad_ok += 1
        else:
            failures.append(f"number malformed {line!r}: want error, got {ans!r}")
    lines.append(
        f"Malformed num requests answered error: {bad_ok} of "
        f"{len(NUM_MALFORMED)}"
    )
    empty_ok = 0
    answers, _ = ask_all(["num", "num "])
    for ans in answers:
        if ans == "none":
            empty_ok += 1
        else:
            failures.append(f"empty num request: want none, got {ans!r}")
    lines.append(f"Num requests with no codes answered none: {empty_ok} of 2")
    # 7. the printing limit: plain notation past 10,000 digits
    # answers none, and a value at the limit still prints. The
    # boundary answer holds 10,000 digits, far more text than
    # its request, so this batch runs with a larger output cap.
    limit_cases = [
        ("1e999999999", None),
        ("1e-999999999", None),
        ("1e10000", None),
        ("1e9999", canonical_number("1e9999")),
    ]
    limit_ok = 0
    answers, problems = ask_all(
        [num_request(t) for t, _ in limit_cases], cap_factor=8192
    )
    for problem in problems:
        failures.append(f"number limit: tool problem: {problem}")
    for (text, want), ans in zip(limit_cases, answers):
        if want is None:
            good = ans == "none"
            want_desc = "none"
        else:
            good = answer_text(ans) == want
            want_desc = f"ok with {len(want)} digits"
        if good:
            limit_ok += 1
        else:
            failures.append(
                f"number limit {text!r}: want {want_desc}, got "
                f"{(ans or '')[:60]!r}"
            )
    lines.append(
        f"Number printing limit cases (over 10000 digits answers "
        f"none, at the limit prints): {len(limit_cases)} inputs, "
        f"{limit_ok} agreements"
    )
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
    lines, failures = run_numbers()
    all_lines += lines
    all_failures += failures

    lean_version = subprocess.run(
        ["lake", "env", "lean", "--version"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=120,
    ).stdout.strip()

    # The axiom check: Json/Proofs/Verify.lean prints the axioms of
    # the five named theorems with `#print axioms`. Its output
    # goes into the results file, in the Axiom check section.
    # A failed run, a missing line, or a line that does not name
    # its theorem is recorded as a failure, never passed over.
    axiom_names = [
        "Json.Proofs.parse_print",
        "Json.NumProofs.read_print",
        "Json.NumProofs.readNumber_wf",
        "Json.NumProofs.read_print_of_read",
        "Json.NumProofs.canonical_eq_of_value_eq",
    ]
    axiom_run = subprocess.run(
        ["lake", "env", "lean", "Json/Proofs/Verify.lean"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=600,
    )
    axiom_lines = [
        line for line in axiom_run.stdout.strip().splitlines() if line.strip()
    ]
    if (
        axiom_run.returncode != 0
        or len(axiom_lines) != len(axiom_names)
        or any(
            name not in line
            for name, line in zip(axiom_names, axiom_lines)
        )
    ):
        all_failures.append(
            "axiom check: running Json/Proofs/Verify.lean gave "
            f"status {axiom_run.returncode} and lines {axiom_lines!r}"
        )

    out = ["# Test results", ""]
    out.append("Written by `tests/run_tests.py`. Rerun it to check these numbers.")
    out.append("")
    out.append(
        f"- Oracle: Python {sys.version.split()[0]} `json` (strict constants)"
    )
    out.append(f"- Lean: {lean_version}")
    out.append(f"- Seed: {args.seed}")
    out.append(f"- Number seed: {NUM_SEED}")
    for line in all_lines:
        out.append(f"- {line}")
    out.append("")
    out.append("## Axiom check")
    out.append("")
    out.append(
        "The output of `#print axioms` for the five named theorems, "
        "from `lake env lean Json/Proofs/Verify.lean`:"
    )
    out.append("")
    for line in axiom_lines:
        out.append(f"- {line}")
    out.append("")
    out.append(f"- Failures: {len(all_failures)}")
    for failure in all_failures[:50]:
        out.append(f"- FAILURE: {failure}")
    RESULTS.write_text("\n".join(out) + "\n", encoding="utf-8")
    print("\n".join(out))
    return 0 if not all_failures else 1


if __name__ == "__main__":
    sys.exit(main())

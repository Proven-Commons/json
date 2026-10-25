# json: a JSON parser and printer, with a proved round trip

A JSON parser and printer in Lean, following RFC 8259. The parser reads a JSON text into a value; the printer writes a value back in one fixed canonical form, with no spaces, object keys in the order held, and strings escaped by fixed rules. The main claim is proved: parsing what the printer wrote returns the same value. The tests run the parser against JSONTestSuite and against Python's `json` module; see `tests/TEST-RESULTS.md` for the counts.

Status: in progress. The specification has not yet been approved by a reviewer apart from its author, and no statement file (`Spec.lean`) has been added by a reviewer, so this is not verified.

## What is proved

The definitions are in `Json/Value.lean` (the value type, the printer, and the well-formedness rules) and `Json/Parse.lean` (the parser). The proofs are in `Proofs/RoundTrip.lean`.

| Claim | Theorem |
|-------|---------|
| Parsing the printed form of a well formed value gives the value back. | `Json.Proofs.parse_print` |
| The same, in the three-part form the induction proves: one statement for a value, one for the inside of an array, one for the inside of an object. | `Json.Proofs.key` |
| Reading back a printed number's text, when the text after it cannot continue a number, gives the text back whole. | `Json.Proofs.parseNumber_append` |
| Reading back an escaped string body gives the string back, escapes and all. | `Json.Proofs.parseStrBody_escapeAll` |

A value is well formed when a number's text matches the RFC 8259 number grammar and every value inside an array or object is well formed too. Strings and keys need no further condition. `parse_print` checks against the standard axioms only (`propext`, `Classical.choice`, `Quot.sound`), which a reader can confirm with `#print axioms Json.Proofs.parse_print`.

The command-line tool in `Main.lean` calls these functions directly.

## What is not proved

- That the parser accepts every text RFC 8259 allows, and rejects every text it forbids. The round trip does not need either, so neither is proved. JSONTestSuite and the differential tests check that behaviour instead, and the results file records the outcome, including any failure.
- Anything about numeric value. A number is held as its source text, checked against the number grammar, and printed word for word. The library never converts it to a number, so it cannot say that two different texts, such as `1e2` and `100`, are the same number.
- Object lookup. Duplicate keys are kept as written, in order, and no claim is made about which pair a lookup would find. There is no lookup function.
- Reading requests and printing answers in `Main.lean`: splitting lines, the decimal parser, and the check that a code is a Unicode scalar value. The tests cover them, malformed requests included.
- Speed. The code works on lists of characters, which suits proofs, not large data. The parser also bounds nesting by the length of the input text, which very deep inputs can reach.

Two deliberate choices, also stated in `SPEC.md`:

- A lone surrogate escape (such as `\ud800` with no low surrogate escape after it) is rejected. A Lean character is one Unicode scalar value and cannot hold half a pair. Python's `json` module accepts such escapes; the tests count this as a named difference, not a failure.
- A high surrogate escape must be followed at once by a low surrogate escape, and the pair is read as the one character it encodes. On printing, that character is written raw, never as a pair of escapes.

## What you must trust

- The Lean kernel, which checks the proofs.
- The Lean compiler, with the C compiler and linker shipped with it, and the runtime, which turn the proved definitions into the program that runs.
- Lean's core library, including the compiled code it puts in place of some definitions the proofs reason about.
- The operating system and hardware it runs on.
- Python's standard library, as the oracle in the differential tests, and JSONTestSuite, as a set of texts whose expected outcomes are maintained by its authors. The results file names the versions used.

This project has no dependencies beyond Lean itself.

## Run it

Needs Linux and [elan](https://github.com/leanprover/elan). Build, then feed request lines to the tool:

```
lake build
echo "parse 91,34,97,34,93" | .lake/build/bin/json
```

That request is the text `["a"]` as character codes, and the answer is `ok:91,34,97,34,93`. A text the parser rejects, such as the single code `120` (the letter `x`), answers `none`. A malformed request answers `error`. See `SPEC.md` for the full protocol.

## Re-check it

Needs Linux, elan, and Python 3.11 or later.

```
lake build
grep -rn "sorry" --include="*.lean" Json Proofs Main.lean Json.lean Proofs.lean
python3 tests/run_tests.py
```

The grep should print nothing: there is no `sorry` anywhere. The test script rebuilds the tool, runs JSONTestSuite if a clone is found (set the environment variable `JSONTESTSUITE_DIR` to its path; without one, that part of the run says so in the results file), runs the differential tests against Python's `json` module with a fixed seed, and writes the counts to `tests/TEST-RESULTS.md`.

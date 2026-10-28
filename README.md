# json: a JSON parser and printer, with a proved round trip

A JSON parser and printer in Lean, following RFC 8259. The parser reads a JSON text into a value; the printer writes a value back in one fixed canonical form, with no spaces, object keys in the order held, and strings escaped by fixed rules. The main claim is proved: parsing what the printer wrote returns the same value. Slice 2 adds a number value layer: a single number text can be read as an exact decimal value, held in a canonical normalized form, and printed back as one canonical text in plain notation. Its round trip is proved too. The tests run the parser against JSONTestSuite and against Python's `json` module, and the number layer against Python's `decimal` module; see `tests/TEST-RESULTS.md` for the counts.

Status: in progress. The specification has not yet been approved by a reviewer apart from its author, and no statement file (`Spec.lean`) has been added by a reviewer, so this is not verified.

## What is proved

The definitions are in `Json/Value.lean` (the value type, the printer, and the well-formedness rules) and `Json/Parse.lean` (the parser). The number layer is in `Json/Number.lean` (the decimal value, its reader, and its canonical printer). The proofs are in `Proofs/RoundTrip.lean` and `Proofs/NumRoundTrip.lean`.

| Claim | Theorem |
|-------|---------|
| Parsing the printed form of a well formed value gives the value back. | `Json.Proofs.parse_print` |
| The same, in the three-part form the induction proves: one statement for a value, one for the inside of an array, one for the inside of an object. | `Json.Proofs.key` |
| Reading back a printed number's text, when the text after it cannot continue a number, gives the text back whole. | `Json.Proofs.parseNumber_append` |
| Reading back an escaped string body gives the string back, escapes and all. | `Json.Proofs.parseStrBody_escapeAll` |
| Reading the canonical text of a well formed decimal value gives the value back. | `Json.NumProofs.read_print` |
| Every value the number reader returns is well formed (canonical zero, or a significand with no trailing zero). | `Json.NumProofs.readNumber_wf` |
| The canonical text of a text's value re-reads to that value. | `Json.NumProofs.read_print_of_read` |
| Two texts with the same value have the same canonical text. | `Json.NumProofs.canonical_eq_of_value_eq` |

A document value is well formed when a number's text matches the RFC 8259 number grammar and every value inside an array or object is well formed too. Strings and keys need no further condition. A decimal value is well formed when it is held in the canonical form: the zero value as sign positive, significand `0`, exponent `0`, and a nonzero value with no trailing zero in its significand. The value round trip needs no bound on the value: the canonical text is finite for every held value. `parse_print` checks against the standard axioms only (`propext`, `Classical.choice`, `Quot.sound`), and `Json.NumProofs.read_print` against `propext` and `Quot.sound` only, which a reader can confirm with `#print axioms`.

The command-line tool in `Main.lean` calls these functions directly.

## What is not proved

- That the parser accepts every text RFC 8259 allows, and rejects every text it forbids. The round trip does not need either, so neither is proved. JSONTestSuite and the differential tests check that behaviour instead, and the results file records the outcome, including any failure.
- That the number reader accepts exactly the texts the grammar accepts, and computes the mathematically right value for each one. The round trip and the normalization of what the reader returns are proved; the agreement with the grammar and with the value of a text is checked by the tests against Python's `decimal` module instead, over fixed cases, random texts in every grammar shape, and groups of spellings of one value.
- Numeric value inside documents. A number in a document is still held as its source text, checked against the number grammar, and printed word for word. The value layer is separate: it reads one number text at a time, through the `num` request, and documents do not use it.
- Object lookup. Duplicate keys are kept as written, in order, and no claim is made about which pair a lookup would find. There is no lookup function.
- Reading requests and printing answers in `Main.lean`: splitting lines, the decimal parser, and the check that a code is a Unicode scalar value. The tests cover them, malformed requests included.
- Speed. The code works on lists of characters, which suits proofs, not large data. The parser also bounds nesting by the length of the input text, which very deep inputs can reach. One printing limit does apply at the tool: the `num` operation answers `none` when the plain notation of a value would hold more than 10,000 digits, instead of expanding a huge exponent into zeros. That limit is the tool's alone. The number still reads as a value, and the library printer and its round trip proof carry no bound.

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

That request is the text `["a"]` as character codes, and the answer is `ok:91,34,97,34,93`. A text the parser rejects, such as the single code `120` (the letter `x`), answers `none`. A malformed request answers `error`. The `num` operation reads one number text as a value and answers with its canonical text: `echo "num 49,46,53,48" | .lake/build/bin/json` asks for the value of `1.50` and answers `ok:49,46,53`, the codes of `1.5`. See `SPEC.md` for the full protocol.

## Re-check it

Needs Linux, elan, and Python 3.11 or later.

```
lake build
grep -rn "sorry" --include="*.lean" Json Proofs Main.lean Json.lean Proofs.lean
python3 tests/run_tests.py
```

The grep should print nothing: there is no `sorry` anywhere. The test script rebuilds the tool, runs JSONTestSuite if a clone is found (set the environment variable `JSONTESTSUITE_DIR` to its path; without one, that part of the run says so in the results file), runs the differential tests against Python's `json` module with a fixed seed, and writes the counts to `tests/TEST-RESULTS.md`.

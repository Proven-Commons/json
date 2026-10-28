# json: a JSON parser and printer, with a proved round trip

Status: in-progress

A JSON parser and printer in Lean, following RFC 8259. The parser reads a JSON text into a value; the printer writes a value back in one fixed canonical form, with no spaces, object keys in the order held, and strings escaped by fixed rules. The main claim is proved: parsing what the printer wrote returns the same value. Slice 2 adds a number value layer: a single number text can be read as an exact decimal value, held in a canonical normalized form, and printed back as one canonical text in plain notation. Its round trip is proved too. The definitions are in `Json/Value.lean` (the value type, the printer, and the well-formedness rules), `Json/Parse.lean` (the parser), and `Json/Number.lean` (the decimal value, its reader, and its canonical printer). The rules are written out in `SPEC.md`.

The statements a reviewer approves are in `Spec.lean`, with their proofs in `Proofs/SpecProofs.lean`. No reviewer has approved them yet, so this project is not called verified.

## How to run it

Needs Linux and [elan](https://github.com/leanprover/elan). Build, then feed request lines to the tool:

```
lake build
echo "parse 91,34,97,34,93" | .lake/build/bin/json
```

That request is the text `["a"]` as character codes, and the answer is `ok:91,34,97,34,93`. A text the parser rejects, such as the single code `120` (the letter `x`), answers `none`. A malformed request answers `error`. The `num` operation reads one number text as a value and answers with its canonical text: `echo "num 49,46,53,48" | .lake/build/bin/json` asks for the value of `1.50` and answers `ok:49,46,53`, the codes of `1.5`. See `SPEC.md` for the full protocol.

`python3 tests/run_tests.py` rebuilds the tool, runs JSONTestSuite if a clone is found (set the environment variable `JSONTESTSUITE_DIR` to its path; without one, that part of the run says so in the results file), runs the differential tests against Python's `json` module with a fixed seed, runs the number layer against Python's `decimal` module, and writes the counts to `tests/TEST-RESULTS.md`.

## What is proved

Each claim below names the theorem behind it. The theorems are stated in `Spec.lean` (the challenge file, where they end in `sorry`) and proved in `Proofs/SpecProofs.lean`, under the same names. `comparator.json` lists all of them.

| Claim | Theorem |
|-------|---------|
| Parsing the printed form of a well formed value gives the value back. | `Spec.parse_print` |
| Reading the canonical text of a well formed decimal value gives the value back. | `Spec.read_print` |
| Every value the number reader returns is well formed (canonical zero, or a significand with no trailing zero). | `Spec.readNumber_wf` |
| The canonical text of a text's value re-reads to that value. | `Spec.read_print_of_read` |
| Two texts with the same value have the same canonical text. | `Spec.canonical_eq_of_value_eq` |
| Characters standing after a complete value, past the whitespace the grammar allows, are refused: the text `1 x`. | `Spec.rejects_trailing_after_value` |
| A literal that is none of `true`, `false`, and `null` is refused: the text `trux`. | `Spec.rejects_bad_literal` |
| A number with a leading zero inside a document is refused: the text `01`. | `Spec.rejects_leading_zero_in_document` |
| A bare minus sign is refused as a number text: the text `-`. | `Spec.rejects_num_lone_minus` |
| A number text with a leading zero is refused: the text `01`. | `Spec.rejects_num_leading_zero` |
| A number text ending in a point with no digit after it is refused: the text `1.`. | `Spec.rejects_num_trailing_point` |
| A number text with a point and no integer part before it is refused: the text `.5`. | `Spec.rejects_num_leading_point` |
| A number text whose exponent letter has no digits after it is refused: the text `1e`. | `Spec.rejects_num_bare_exponent` |
| A number text whose exponent sign has no digits after it is refused: the text `1e+`. | `Spec.rejects_num_exponent_sign_only` |
| A number text with a leading plus sign is refused: the text `+1`. | `Spec.rejects_num_leading_plus` |
| A number text with a letter where a digit must stand is refused: the text `1a`. | `Spec.rejects_num_nondigit` |

A document value is well formed when a number's text matches the RFC 8259 number grammar and every value inside an array or object is well formed too. Strings and keys need no further condition. A decimal value is well formed when it is held in the canonical form: the zero value as sign positive, significand `0`, exponent `0`, and a nonzero value with no trailing zero in its significand. The value round trip needs no bound on the value: the canonical text is finite for every held value.

The five claims rest on the proofs in `Proofs/RoundTrip.lean` and `Proofs/NumRoundTrip.lean`, where they are `Json.Proofs.parse_print`, `Json.NumProofs.read_print`, `Json.NumProofs.readNumber_wf`, `Json.NumProofs.read_print_of_read`, and `Json.NumProofs.canonical_eq_of_value_eq`. `Spec.parse_print` checks against the standard axioms only (`propext`, `Classical.choice`, `Quot.sound`); `Spec.read_print`, `Spec.readNumber_wf`, and `Spec.read_print_of_read` against `propext` and `Quot.sound` only; and `Spec.canonical_eq_of_value_eq` against `propext` only. A reader can confirm this with `#print axioms`, or by running `lake env lean Proofs/Verify.lean`. The test harness writes that output into the Axiom check section of `tests/TEST-RESULTS.md` on every run. The refusal theorems are single inputs checked in the kernel with `decide +kernel`.

The command line tool in `Main.lean` calls `Json.parse`, `Json.print`, `Json.readNumber`, and `Json.printVal` directly, the same functions the theorems are about.

## What is not proved

- That the parser accepts every text RFC 8259 allows, and rejects every text it forbids. The round trip does not need either, so neither is proved. JSONTestSuite and the differential tests check that behaviour instead, and the results file records the outcome, including any failure.
- That the number reader accepts exactly the texts the grammar accepts, and computes the mathematically right value for each one. The round trip and the normalization of what the reader returns are proved; the agreement with the grammar and with the value of a text is checked by the tests against Python's `decimal` module instead, over fixed cases, random texts in every grammar shape, and groups of spellings of one value.
- Numeric value inside documents. A number in a document is still held as its source text, checked against the number grammar, and printed word for word. The value layer is separate: it reads one number text at a time, through the `num` request, and documents do not use it.
- Object lookup. Duplicate keys are kept as written, in order, and no claim is made about which pair a lookup would find. There is no lookup function.
- Reading requests and printing answers in `Main.lean`: splitting lines, the decimal parser, and the check that a code is a Unicode scalar value. The tests cover them, malformed requests included.
- Speed. The code works on lists of characters, which suits proofs, not large data. The parser also bounds nesting by the length of the input text, which very deep inputs can reach. One printing limit does apply at the tool: the `num` operation answers `none` when the plain notation of a value would hold more than 10,000 digits, instead of expanding a huge exponent into zeros. That limit is the tool's alone. The number still reads as a value, and the library printer and its round trip proof carry no bound.
- The refusal theorems pin single inputs only. That each grammar rule refuses every text that breaks it is a test matter, not a proof.
- A lone surrogate escape (such as `\ud800` with no low surrogate escape after it) is rejected. A Lean character is one Unicode scalar value and cannot hold half a pair. Python's `json` module accepts such escapes; the tests count this as a named difference, not a failure.
- A high surrogate escape must be followed at once by a low surrogate escape, and the pair is read as the one character it encodes. On printing, that character is written raw, never as a pair of escapes.

## What you must trust

- The Lean kernel (Lean 4.35.0, pinned in `lean-toolchain`), which checks every proof.
- The Lean compiler, with the C compiler and linker shipped with it, which turns the proved definitions into the program that runs.
- The Lean runtime, which runs that program.
- The hardware the program runs on.
- Every dependency in `lake-manifest.json`: the manifest lists no packages, so there are no library dependencies to trust beyond the Lean toolchain itself.
- Lean's core library, including the compiled code it puts in place of some definitions the proofs reason about.
- The operating system the program runs on.
- That `SPEC.md` states the reading of RFC 8259 you intend. The proofs are about the parser, the printer, and the number layer in this repo following each other exactly; the fidelity of the spec to the RFC is a reading, pinned in `SPEC.md` where the RFC leaves a choice open.
- Python's standard library in the tests: the `json` module as the document oracle, and the `decimal` module as the value oracle. Also JSONTestSuite, as a set of texts whose expected outcomes are maintained by its authors. Both are evidence, not proof. The results file names the versions used.
- The line handling in `Main.lean` (splitting a request line, reading decimal codes, the check that a code is a Unicode scalar value). The tests drive it, and no proof covers it.
- There are no exceptions to item 4 of the bar: the project uses none of the features it forbids.

## Re-check it

1. `lake comparator --paranoid`: builds the challenge file `Spec.lean` and the proofs in a sandbox and checks that each theorem named in `comparator.json` proves exactly the statement in the challenge file, uses no axiom but the three standard ones, and is accepted by Lean's kernel and every other kernel shipped with Lean.
2. `python3 tests/run_tests.py`: JSONTestSuite if a clone is found, the differential against Python's `json` module, the number layer against Python's `decimal` module, and the axiom check, with counts and any failures written to `tests/TEST-RESULTS.md`.
3. `lake build`: the library, the proofs, and the tool build clean, and `lake env lean Proofs/Verify.lean` prints the axiom list for the five headline theorems.
4. Read `SPEC.md` against RFC 8259 and check the pinned readings are the ones you want.

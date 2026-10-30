# Specification: json

A JSON parser and printer in Lean, following RFC 8259. A reviewer who did not write this specification approves it, together with the statement file. The statements are in `Json/Spec.lean` and their proofs are in `Json/Proofs/SpecProofs.lean`; no reviewer has approved them yet, so nothing here counts toward the verified bar yet.

Text is `List Char`. A Lean `Char` is one Unicode scalar value, so a string in this library can never hold half of a surrogate pair. That fact shapes two choices below.

## Values

One value type:

- `null`
- `bool` (true or false)
- `num`: a number, held as its source text (a list of characters)
- `str`: a string, held as a list of characters
- `arr`: a list of values
- `obj`: a list of key and value pairs, each key a list of characters

Object pairs are kept in the order they are held. Duplicate keys are kept as written. This library makes no claim about looking a key up.

## Numbers

A number is held as its source text, checked against the RFC 8259 number grammar:

- an optional minus sign;
- an integer part: either `0` on its own, or a digit from `1` to `9` followed by any digits (no leading zeros, and a bare minus with no digits is not a number);
- an optional fraction part: a point followed by at least one digit;
- an optional exponent part: `e` or `E`, an optional sign, and at least one digit.

The printer writes the text back word for word, so a number round trips exactly. Inside a document, this library makes no claim about the numeric value of the text: it does not convert a number to an integer, a fraction, or a float, and it does not compare numbers.

### The number value layer (slice 2)

Separate from documents, a single number text can also be read as a value. A value is an exact decimal:

- a sign: negative or not;
- a significand: a natural number;
- an exponent: an integer, the power of ten.

The value is the sign times the significand times ten to the exponent. A value is held in one canonical form:

- the zero value is held as sign positive, significand `0`, exponent `0`. Every spelling of zero reads to this one value, including `-0` and `0.0e5`;
- a nonzero value is held normalized: its significand has no trailing zero (the last digit is not `0`).

Reading a number text computes the value. The digits of the integer part and the fraction part fold into the significand, the exponent starts as the written exponent minus the number of fraction digits, and then trailing zeros of the significand are divided out into the exponent. A text whose digits are all zero collapses to the canonical zero. Reading turns away every text the grammar above turns away.

The canonical text of a value is written under one rule, in plain decimal notation always, never in exponent notation:

- work out where the point falls from the significand's digits and the exponent;
- if the point falls past the last digit, write the digits and pad with zeros after them, with no point;
- if the point falls inside the digits, write it there;
- if the point falls before the first digit, write `0`, a point, the zeros the point position calls for, and then the digits;
- a negative nonzero value gets a minus sign in front. Zero writes as `0`.

The command-line tool sets one limit on this printing. If the plain notation of a value would hold more than 10,000 digits, the `num` operation answers `none` instead of printing it. The limit sits far past any number a real JSON document carries, and it stops a short text such as `1e999999999` from asking for unbounded time and memory. This is a refusal to print, not a reading error: the text still reads as a number, and the value layer itself sets no bound. A `parse` request is not affected either, because a number inside a document prints word for word and never expands an exponent.

Because the held form is unique per value, two texts with the same value have the same canonical text.

## Strings

On reading:

- The escapes are the RFC set: `\"`, `\\`, `\/`, `\b`, `\f`, `\n`, `\r`, `\t`, and `\uXXXX` with four hex digits.
- A `\uXXXX` escape in the high surrogate range (U+D800 to U+DBFF) must be followed at once by a `\uXXXX` escape in the low surrogate range (U+DC00 to U+DFFF). The pair combines into one character.
- A lone surrogate escape is rejected, whether high or low. A Lean `Char` cannot hold one, and this library rejects the text rather than inventing a replacement character.
- A raw control character (below U+0020) inside a string is rejected. Control characters must be escaped.

On printing, a string is written in one fixed form:

- `"` as `\"` and `\` as `\\`;
- U+0008 as `\b`, U+0009 as `\t`, U+000A as `\n`, U+000C as `\f`, U+000D as `\r`;
- any other character below U+0020 as `\u00XX` with lowercase hex digits;
- every other character raw, including non-ASCII characters. A character outside the basic multilingual plane prints as itself, never as a surrogate pair of escapes.

## Grammar and whitespace

The parser reads the RFC 8259 grammar:

- Whitespace is only space, tab, line feed, and carriage return. It may appear before and after a value and around the structural characters `[ ] { } : ,`.
- An array is values split by commas, with no trailing comma. An object is key and value pairs split by commas, with no trailing comma. A key must be a string.
- Text after the value, beyond whitespace, is rejected. The parser never reads past the end of its input: a text that ends in the middle of a value is rejected.
- The top level is one value of any kind, as RFC 8259 allows.

The printer writes a value with no spaces anywhere: commas and colons with nothing around them, arrays in brackets, objects in braces.

## The claim

The proved claim is a round trip: for every well formed value, parsing what the printer wrote returns the same value. Well formed means the value follows the rules above: a number's text matches the number grammar, and every value inside an array or object is well formed too. Strings and keys need no further condition: every list of characters prints and reads back.

The number layer carries its own proved claims:

- Value round trip: for every well formed decimal value (held in the canonical form above), reading its canonical text gives the value back. No bound on the value is needed: the digits and the zero padding are finite for every held value, so the canonical text is finite and the reader takes it whole. The 10,000 digit limit above belongs to the command-line tool's `num` operation only. It is not part of this claim and it does not change the library printer or this theorem.
- Every value the reader returns is well formed, so the canonical text of a text's value re-reads to that same value.
- Two texts with the same value have the same canonical text.

No claim is made that the parser accepts every text the RFC grammar allows, or rejects every text it forbids, beyond what the round trip needs. The test suite checks that behaviour against JSONTestSuite and against Python's `json` module, and the results record the counts. For the number layer, the tests check the reader and the canonical printer against Python's `decimal` module as the value oracle, over fixed cases, random texts in every grammar shape, groups of spellings of one value, and grammar rejections.

## The command-line tool

`Main.lean` reads one request per line. There are two operations. `parse`: the request is the word `parse`, a space, and the character codes of a JSON text as comma-separated decimal numbers. The answer is `ok:` followed by the character codes of the canonical print of the parsed value, or `none` when the text is rejected. `num`: the request is the word `num`, a space, and the character codes of a number text. The answer is `ok:` followed by the character codes of the canonical text of the text's value, under the number layer above, or `none` when the text is not a number by the grammar. The answer is also `none` when the plain notation of the value would hold more than 10,000 digits, the printing limit stated in the number layer above. A malformed request line prints `error`. Codes that are not Unicode scalar values make the request malformed.

## Properties and their theorems

Each property a reader can check in the page (`README.md`) names its theorem. The theorems are stated in `Json/Spec.lean` and proved in `Json/Proofs/SpecProofs.lean`. The refusal theorems are single inputs, one for each named rejection shape in the test harness; the tests in `tests/` cover each rule on many more inputs.

| Property | Theorem |
|----------|---------|
| Parsing the printed form of a well formed value gives the value back | `Json.Spec.parse_print` |
| Reading the canonical text of a well formed decimal value gives the value back | `Json.Spec.read_print` |
| Every value the number reader returns is well formed | `Json.Spec.readNumber_wf` |
| The canonical text of a text's value re-reads to that value | `Json.Spec.read_print_of_read` |
| Two texts with the same value have the same canonical text | `Json.Spec.canonical_eq_of_value_eq` |
| Characters after a complete value, past the allowed whitespace, are refused | `Json.Spec.rejects_trailing_after_value` |
| A literal outside `true`, `false`, and `null` is refused | `Json.Spec.rejects_bad_literal` |
| A leading zero in a number inside a document is refused | `Json.Spec.rejects_leading_zero_in_document` |
| A bare minus sign is refused as a number text | `Json.Spec.rejects_num_lone_minus` |
| A leading zero in a number text is refused | `Json.Spec.rejects_num_leading_zero` |
| A point with no digit after it ends no number text | `Json.Spec.rejects_num_trailing_point` |
| A point with no integer part before it starts no number text | `Json.Spec.rejects_num_leading_point` |
| An exponent letter with no digits after it is refused | `Json.Spec.rejects_num_bare_exponent` |
| An exponent sign with no digits after it is refused | `Json.Spec.rejects_num_exponent_sign_only` |
| A leading plus sign is refused | `Json.Spec.rejects_num_leading_plus` |
| A letter where a digit must stand is refused | `Json.Spec.rejects_num_nondigit` |

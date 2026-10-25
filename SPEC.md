# Specification: json

A JSON parser and printer in Lean, following RFC 8259. A reviewer who did not write this specification approves it, together with any statement file a reviewer adds later. No such file exists yet, so nothing here counts toward the verified bar yet.

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

The printer writes the text back word for word, so a number round trips exactly. This library makes no claim about the numeric value of the text: it does not convert a number to an integer, a fraction, or a float, and it does not compare numbers.

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

No claim is made that the parser accepts every text the RFC grammar allows, or rejects every text it forbids, beyond what the round trip needs. The test suite checks that behaviour against JSONTestSuite and against Python's `json` module, and the results record the counts.

## The command-line tool

`Main.lean` reads one request per line. The only operation is `parse`: the request is the word `parse`, a space, and the character codes of a JSON text as comma-separated decimal numbers. The answer is `ok:` followed by the character codes of the canonical print of the parsed value, or `none` when the text is rejected. A malformed request line prints `error`. Codes that are not Unicode scalar values make the request malformed.

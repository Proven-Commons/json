/-
  The specification as Lean statements: the challenge file.

  A reviewer who did not write this file approves it, and `bar.toml`
  records the SHA-256 it had then. The proofs live in `Proofs`
  (`Proofs/SpecProofs.lean`); `lake comparator` checks that each one
  proves exactly the statement written here. The `sorry` below is
  expected in this file only.

  The statements use only the definitions in `Json/Value.lean`,
  `Json/Parse.lean`, and `Json/Number.lean`, the code under proof
  named in `bar.toml`. No definition of their own is needed, so
  this project has no `Spec/Defs.lean`.
-/

import Json

open Json

/-! ## The document round trip

The headline claim of the first slice, the statement of
`Json.Proofs.parse_print` in `Proofs/RoundTrip.lean`, over the
same well formedness predicate, `Json.WF`. -/

/-- Parsing the printed form of a well formed value gives the
    value back. So a printer that wrote nothing, or wrote
    something shorter, fails this statement. -/
theorem Spec.parse_print {v : Json} (hv : WF v) :
    parse (print v) = some v := sorry

/-! ## The number value layer

The claims of the second slice, the statements of the theorems
of the same names in `Proofs/NumRoundTrip.lean`, over the
canonical form predicate, `Json.WFVal`. -/

/-- Reading the canonical text of a well formed decimal value
    gives the value back. -/
theorem Spec.read_print {v : DecVal} (hv : WFVal v) :
    readNumber (printVal v) = some v := sorry

/-- Every value the number reader returns is well formed:
    canonical zero, or a significand with no trailing zero. -/
theorem Spec.readNumber_wf {cs : List Char} {v : DecVal}
    (h : readNumber cs = some v) : WFVal v := sorry

/-- The canonical text of a text's value re-reads to that
    value. -/
theorem Spec.read_print_of_read {cs : List Char} {v : DecVal}
    (h : readNumber cs = some v) :
    readNumber (printVal v) = some v := sorry

/-- Two texts with the same value have the same canonical
    text. -/
theorem Spec.canonical_eq_of_value_eq {t1 t2 : List Char}
    {v : DecVal} (h1 : readNumber t1 = some v)
    (h2 : readNumber t2 = some v) :
    canonicalText t1 = canonicalText t2 := sorry

/-! ## Refused inputs: documents

Single texts the document reader refuses, one for each headline
rule of `SPEC.md`. Each input is one of the named rejection
shapes the test harness checks. The differential tests and
JSONTestSuite cover these rules on many more inputs; these
statements pin them so a reader of the specification can check
each rule against one concrete case. -/

/-- Characters standing after a complete value, past the
    whitespace the grammar allows, are refused: here `1 x`. -/
theorem Spec.rejects_trailing_after_value :
    (parse (['1', ' ', 'x'] : List Char)).isSome = false := sorry

/-- A literal that is none of `true`, `false`, and `null` is
    refused: here `trux`. -/
theorem Spec.rejects_bad_literal :
    (parse (['t', 'r', 'u', 'x'] : List Char)).isSome
      = false := sorry

/-- A number with a leading zero inside a document is refused:
    here `01`, where the zero alone is the whole integer part
    the grammar allows, and the `1` is left standing after the
    value. -/
theorem Spec.rejects_leading_zero_in_document :
    (parse (['0', '1'] : List Char)).isSome = false := sorry

/-! ## Refused inputs: number texts

Single texts the number reader refuses, from the named
rejection set in the test harness (`NUM_REJECTIONS` in
`tests/run_tests.py`). -/

/-- A bare minus sign is refused: a sign with no digits is not
    a number. -/
theorem Spec.rejects_num_lone_minus :
    (readNumber (['-'] : List Char)).isSome = false := sorry

/-- A leading zero is refused: here `01`. -/
theorem Spec.rejects_num_leading_zero :
    (readNumber (['0', '1'] : List Char)).isSome = false := sorry

/-- A point with no digit after it is refused: here `1.`. -/
theorem Spec.rejects_num_trailing_point :
    (readNumber (['1', '.'] : List Char)).isSome = false := sorry

/-- A point with no integer part before it is refused: here
    `.5`. -/
theorem Spec.rejects_num_leading_point :
    (readNumber (['.', '5'] : List Char)).isSome = false := sorry

/-- An exponent letter with no digits after it is refused:
    here `1e`. -/
theorem Spec.rejects_num_bare_exponent :
    (readNumber (['1', 'e'] : List Char)).isSome = false := sorry

/-- An exponent sign with no digits after it is refused: here
    `1e+`. -/
theorem Spec.rejects_num_exponent_sign_only :
    (readNumber (['1', 'e', '+'] : List Char)).isSome
      = false := sorry

/-- A leading plus sign is refused: the grammar allows a minus
    only. Here `+1`. -/
theorem Spec.rejects_num_leading_plus :
    (readNumber (['+', '1'] : List Char)).isSome = false := sorry

/-- A letter standing where a digit must be is refused: here
    `1a`, where the `a` is left over after the number part. -/
theorem Spec.rejects_num_nondigit :
    (readNumber (['1', 'a'] : List Char)).isSome = false := sorry

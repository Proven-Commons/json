/-
  Proofs of the statements in `Spec.lean`, under the same names.

  The five claims are the theorems proved in
  `Proofs/RoundTrip.lean` and `Proofs/NumRoundTrip.lean`. The
  refusals are single inputs, checked in the kernel with
  `decide +kernel`: no native evaluation, which the bar forbids.
-/

import Json
import Proofs.RoundTrip
import Proofs.NumRoundTrip

open Json

theorem Spec.parse_print {v : Json} (hv : WF v) :
    parse (print v) = some v :=
  Json.Proofs.parse_print hv

theorem Spec.read_print {v : DecVal} (hv : WFVal v) :
    readNumber (printVal v) = some v :=
  Json.NumProofs.read_print hv

theorem Spec.readNumber_wf {cs : List Char} {v : DecVal}
    (h : readNumber cs = some v) : WFVal v :=
  Json.NumProofs.readNumber_wf h

theorem Spec.read_print_of_read {cs : List Char} {v : DecVal}
    (h : readNumber cs = some v) :
    readNumber (printVal v) = some v :=
  Json.NumProofs.read_print_of_read h

theorem Spec.canonical_eq_of_value_eq {t1 t2 : List Char}
    {v : DecVal} (h1 : readNumber t1 = some v)
    (h2 : readNumber t2 = some v) :
    canonicalText t1 = canonicalText t2 :=
  Json.NumProofs.canonical_eq_of_value_eq h1 h2


theorem Spec.rejects_trailing_after_value :
    (parse (['1', ' ', 'x'] : List Char)).isSome = false := by
  decide +kernel


theorem Spec.rejects_bad_literal :
    (parse (['t', 'r', 'u', 'x'] : List Char)).isSome
      = false := by
  decide +kernel


theorem Spec.rejects_leading_zero_in_document :
    (parse (['0', '1'] : List Char)).isSome = false := by
  decide +kernel


theorem Spec.rejects_num_lone_minus :
    (readNumber (['-'] : List Char)).isSome = false := by
  decide +kernel


theorem Spec.rejects_num_leading_zero :
    (readNumber (['0', '1'] : List Char)).isSome = false := by
  decide +kernel


theorem Spec.rejects_num_trailing_point :
    (readNumber (['1', '.'] : List Char)).isSome = false := by
  decide +kernel


theorem Spec.rejects_num_leading_point :
    (readNumber (['.', '5'] : List Char)).isSome = false := by
  decide +kernel


theorem Spec.rejects_num_bare_exponent :
    (readNumber (['1', 'e'] : List Char)).isSome = false := by
  decide +kernel


theorem Spec.rejects_num_exponent_sign_only :
    (readNumber (['1', 'e', '+'] : List Char)).isSome
      = false := by
  decide +kernel


theorem Spec.rejects_num_leading_plus :
    (readNumber (['+', '1'] : List Char)).isSome = false := by
  decide +kernel


theorem Spec.rejects_num_nondigit :
    (readNumber (['1', 'a'] : List Char)).isSome = false := by
  decide +kernel

/-
  Axiom check for the headline theorems. Building this file
  prints the axioms the proofs depend on. The expected output
  is only the three standard Lean axioms: `propext`,
  `Classical.choice`, `Quot.sound`, or a subset of them. Any
  other name here breaks the verified bar.
-/

import Json.Proofs.RoundTrip
import Json.Proofs.NumRoundTrip

#print axioms Json.Proofs.parse_print
#print axioms Json.NumProofs.read_print
#print axioms Json.NumProofs.readNumber_wf
#print axioms Json.NumProofs.read_print_of_read
#print axioms Json.NumProofs.canonical_eq_of_value_eq

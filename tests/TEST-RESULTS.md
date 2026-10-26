# Test results

Written by `tests/run_tests.py`. Rerun it to check these numbers.

- Oracle: Python 3.12.3 `json` (strict constants)
- Lean: Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)
- Seed: 20261025
- JSONTestSuite: clone found, test_parsing used
- JSONTestSuite y_ files accepted with a stable reprint: 95 of 95
- JSONTestSuite n_ files rejected: 188 of 188
- JSONTestSuite n_ files rejected at the encoding level (bytes not valid UTF-8): 12
- JSONTestSuite i_ files skipped: 35
- Differential inputs: 9007
- Differential agreements: 9007
- Cases where Python accepts a lone surrogate escape and Lean rejects it (named difference): 7
- Malformed requests answered error: 12 of 12
- Requests with no codes answered none: 2 of 2
- Failures: 0

## Axiom check

Recorded on 2026-10-26 against the head of this pull request, on Lean 4.35.0. This slice holds no Verify file. The line below is the output of a file holding `#print axioms Json.Proofs.parse_print` and an import of the proofs, run with `lake env lean` in a copy of this tree after a clean `lake build` (14 jobs).

```text
'Json.Proofs.parse_print' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No other axiom is named, and sorryAx is not named.

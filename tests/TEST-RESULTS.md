# Test results

Written by `tests/run_tests.py`. Rerun it to check these numbers.

- Oracle: Python 3.12.3 `json` (strict constants)
- Lean: Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)
- Seed: 20261025
- Number seed: 20261026
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
- Number fixed cases: 68 inputs, 68 agreements
- Number random cases (seed 20261026): 3000 inputs, 3000 agreements
- Number random bounds: written exponent between -60 and 60, at most 40 digits per text
- Number equal-value groups: 7 groups, 43 spellings, 7 groups with one canonical text
- Number rejections answered none: 35 of 35
- Number canonical texts fed back: 3000 inputs, 3000 agreements
- Malformed num requests answered error: 10 of 10
- Num requests with no codes answered none: 2 of 2
- Failures: 0

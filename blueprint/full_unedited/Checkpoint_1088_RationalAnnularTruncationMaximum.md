# Checkpoint 1088: Simultaneous real-denominator and time maximum with square loss

A single nonnegative integer L2 majorant now controls every dyadic time and every nonnegative real denominator cutoff simultaneously, with the printed square (1+s)^2 loss. The proof uses actual localized multiplier blocks and disjoint Bessel energies for large s, all 33 possible bounded denominator cutoffs for the small indices, and the three finite cutoffs needed at scale1. It invokes exactly the explicit rational smooth/transference and general smooth inputs already recorded at checkpoints1086–1087. No fixed-multiplier clause is credited yet; the full corollary remains partial until that clause is proved.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| RationalAnnularTruncationMaximum.lean | 7 |

- `rationalAnnularTruncationConstant_pos`
- `rational_weightedAnnular_truncation_maximum`
- `rationalAllTruncationConstant_pos`
- `rational_smallIndex_all_thresholds`
- `rational_annular_all_thresholds`
- `sourceRationalTruncationConstant_pos`
- `source_rational_annular_truncation_maximum`

<!-- checkpoint-verification -->

## Verification

All 1155 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4946-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 3482 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1157 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The current complete manuscript upload confirms the independent admissibility coefficient. The full generic sparse recursion is proved under its normal local hypothesis. The unchanged upload and a separate selected copy with the previously approved factor-four application restored are preserved. Four substantive auxiliaries remain partial. Section9 mapping and reductions are now authorized; later analytic and sieve inputs remain explicit. The rational smooth multifrequency theorem together with circle transference is an explicit independent compound hypothesis; its existence is unproved. Its predicate contains no own-paper annular or truncated maximal conclusion. See docs/RATIONAL_MULTIFREQUENCY_BOUNDARY.md.

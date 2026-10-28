# Checkpoint 800: Prove interval inclusion, connected unions and dilation geometry

Proves exact inclusion criteria, endpoint membership, length comparison, connected union via interval hull, and preservation of inclusion under fivefold dilation for actual nonempty integer intervals. These facts support a direct stopping construction with maximal consecutive bad intervals; the output need not depend on a dyadic-grid replacement.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| IntegerIntervalGeometry.lean | 10 |

- `integerInterval_left_mem`
- `integerInterval_last_mem`
- `integerInterval_subset_iff`
- `integerInterval_subset_length`
- `integerInterval_subset_equal_length`
- `integerInterval_hull_mem`
- `integerInterval_subset_hull_left`
- `integerInterval_subset_hull_right`
- `integerInterval_hull_eq_union`
- `integerInterval_five_subset`

<!-- checkpoint-verification -->

## Verification

All 867 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4474-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2263 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 869 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results under their paper hypotheses remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. Lemma 3.21, both conclusions of Theorem 1.1, all displayed clauses of Proposition 4.19 and both clauses of Proposition 6.21 are complete checked implications under their separately recorded independent deep inputs. The square-sign reflection is proved. The whole paper, the stronger printed auxiliary lemmas and the later sparse/ergodic/sieve applications remain unfinished. Proposition 4.19 consumes PrimeAsymptoticInputs, the refined PagePrimeSquareDistributionInputs c, RawPageUniquenessInput c and SmoothCircleBourgainInput C. These are independent raw analytic/data hypotheses, not own-paper operator conclusions or new Lean axioms. Theorem 1.1 retains its separately recorded older fixed-scale inputs and independent ordinary-square global decomposition; reflection is proved.

# Checkpoint 792: Define genuine integer sparse families and the two source forms

Defines nonempty integer intervals, their exact cardinalities, fivefold dilation and support-ball containment. Defines the actual finite-set endpoint and power sparse forms with the printed densities and records sparsity through actual pairwise disjoint major subsets. The parameter is explicit: the preliminary definition uses 1/4 and Theorem 1.3 uses 1/10. Proves elementary positivity and monotonicity of sparsity. These are foundations only; no source sparse theorem is awarded from definitions. The previously completed conditional results remain unchanged.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| SparseIntegerIntervals.lean | 11 |

- `card_points`
- `mem_points`
- `nonempty_points`
- `points_subset_five`
- `five_injective`
- `local_ball_subset_five`
- `integerSparseFamily_mono`
- `integerSparseFamily_empty`
- `integerSparseFamily_singleton`
- `integerEndpointSparseForm_nonneg`
- `integerPowerSparseForm_nonneg`

<!-- checkpoint-verification -->

## Verification

All 859 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4466-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2225 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 861 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results under their paper hypotheses remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. Lemma 3.21, both conclusions of Theorem 1.1, all displayed clauses of Proposition 4.19 and both clauses of Proposition 6.21 are complete checked implications under their separately recorded independent deep inputs. The square-sign reflection is proved. The whole paper, the stronger printed auxiliary lemmas and the later sparse/ergodic/sieve applications remain unfinished. Proposition 4.19 consumes PrimeAsymptoticInputs, the refined PagePrimeSquareDistributionInputs c, RawPageUniquenessInput c and SmoothCircleBourgainInput C. These are independent raw analytic/data hypotheses, not own-paper operator conclusions or new Lean axioms. Theorem 1.1 retains its separately recorded older fixed-scale inputs and independent ordinary-square global decomposition; reflection is proved.

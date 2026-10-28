# Checkpoint 843: Exact high-low restricted distribution deduction

The distributional high-low deduction underlying e:orlicz-optimize is proved for the genuine all-index maximum. Given actual large-scale low and high envelopes with finite p and 2 power budgets, the level set is controlled by t J mass |F|+(2t)^p B_low+4t^2 B_high. The proof finds a violating original scale from the supremum, separates the first J averages, performs the exact threshold union, and applies the proved Chebyshev bounds. It also proves the actual level set finite. The large-scale envelope premises are internal hypotheses of this reusable deduction, not authorized replacements for the paper own high-low existence theorem. Their construction remains open for Section7.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| HighLowRestrictedDistribution.lean | 2 |

- `highLow_restricted_distribution`
- `highLow_restricted_levelset_finite`

<!-- checkpoint-verification -->

## Verification

All 910 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4517-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2471 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 912 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed source results under their paper hypotheses remain unchanged. Lemma 3.21, both conclusions of Theorems 1.1 and 1.3, all displayed clauses of Proposition 4.19 and both clauses of Proposition 6.21 are complete checked implications under their separately recorded independent deep inputs. The square-sign reflection is proved. Theorem 1.3 has actual finite sparse families, disjoint major subsets and the literal full all-cutoff maximum. The three general Section5 auxiliary statements remain partial, and the later Orlicz/ergodic/sieve applications remain unfinished. Proposition 4.19 consumes PrimeAsymptoticInputs, the refined PagePrimeSquareDistributionInputs c, RawPageUniquenessInput c and SmoothCircleBourgainInput C. These are independent raw analytic/data hypotheses, not own-paper operator conclusions or new Lean axioms. Theorem 1.1 retains its separately recorded older fixed-scale inputs and independent ordinary-square global decomposition; reflection is proved. Sparse applications additionally record OrdinarySquareStoppingInput CS and IndependentPrimeMaximalInput as explicit independent analytic boundaries. Their existence and the exact normalization/support/sign adaptations remain unproved; neither predicate contains this paper's endpoint or sparse conclusion.

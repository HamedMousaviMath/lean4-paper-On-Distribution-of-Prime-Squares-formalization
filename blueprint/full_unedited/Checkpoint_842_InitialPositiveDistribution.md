# Checkpoint 842: Actual initial-scale mass and Chebyshev contribution

The initial-scale contribution to the Section7 restricted estimate is proved for actual positive finite averages. Translation injectivity bounds the finite sum of a shifted indicator by its cardinality. The actual complex average therefore has l1 mass at most mass*|F|. The sum over the first J averages has l1 mass at most J*mass*|F|, giving exactly t J mass |F| in the distributional estimate. Generic real power budgets, their actual lp-space specialization, and Chebyshev are also proved. No deep theorem or source high-low existence statement is a hypothesis of these initial-scale results.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| InitialPositiveDistribution.lean | 8 |

- `finite_shift_indicator_sum`
- `positiveAverage_indicator_l1`
- `initialPositiveSum_nonneg`
- `initialPositiveSum_dominates`
- `initialPositiveSum_l1`
- `finiteDistribution_real_power`
- `finitePowerBudget_lp`
- `initialPositiveSum_distribution`

<!-- checkpoint-verification -->

## Verification

All 909 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4516-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2469 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 911 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed source results under their paper hypotheses remain unchanged. Lemma 3.21, both conclusions of Theorems 1.1 and 1.3, all displayed clauses of Proposition 4.19 and both clauses of Proposition 6.21 are complete checked implications under their separately recorded independent deep inputs. The square-sign reflection is proved. Theorem 1.3 has actual finite sparse families, disjoint major subsets and the literal full all-cutoff maximum. The three general Section5 auxiliary statements remain partial, and the later Orlicz/ergodic/sieve applications remain unfinished. Proposition 4.19 consumes PrimeAsymptoticInputs, the refined PagePrimeSquareDistributionInputs c, RawPageUniquenessInput c and SmoothCircleBourgainInput C. These are independent raw analytic/data hypotheses, not own-paper operator conclusions or new Lean axioms. Theorem 1.1 retains its separately recorded older fixed-scale inputs and independent ordinary-square global decomposition; reflection is proved. Sparse applications additionally record OrdinarySquareStoppingInput CS and IndependentPrimeMaximalInput as explicit independent analytic boundaries. Their existence and the exact normalization/support/sign adaptations remain unproved; neither predicate contains this paper's endpoint or sparse conclusion.

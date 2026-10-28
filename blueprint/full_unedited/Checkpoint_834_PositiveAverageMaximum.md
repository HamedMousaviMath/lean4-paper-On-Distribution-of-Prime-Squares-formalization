# Checkpoint 834: Genuine positive averaging maxima and finite layer majorization

The genuine countable maximum of a general positive finite averaging family is constructed and controlled. The family records its actual integer shifts, finite index sets, nonnegative real weights and a uniform mass bound. For bounded inputs the supremum range is proved bounded, every original average is dominated, and the maximum is nonnegative. The complex finite averages satisfy the exact indicator identity and a finite layer-majorization theorem with the correct mass contribution of the bounded remainder. These are proved algebraic and order facts, ready for the actual square, von Mangoldt and prime normalizations. No endpoint or IW estimate is a field of the family.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| PositiveAverageMaximum.lean | 10 |

- `finiteFunction_norm_bound`
- `positiveAverage_norm_bound`
- `positiveMaximal_bdd`
- `positiveMaximal_dominates`
- `positiveMaximal_nonneg`
- `positiveMaximal_norm_bound`
- `finiteIndicator_norm_le_one`
- `positiveMaximal_indicator_bound`
- `positiveAverage_indicator_real`
- `positiveMaximal_layer_majorization`

<!-- checkpoint-verification -->

## Verification

All 901 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4508-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2421 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 903 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed source results under their paper hypotheses remain unchanged. Lemma 3.21, both conclusions of Theorems 1.1 and 1.3, all displayed clauses of Proposition 4.19 and both clauses of Proposition 6.21 are complete checked implications under their separately recorded independent deep inputs. The square-sign reflection is proved. Theorem 1.3 has actual finite sparse families, disjoint major subsets and the literal full all-cutoff maximum. The three general Section5 auxiliary statements remain partial, and the later Orlicz/ergodic/sieve applications remain unfinished. Proposition 4.19 consumes PrimeAsymptoticInputs, the refined PagePrimeSquareDistributionInputs c, RawPageUniquenessInput c and SmoothCircleBourgainInput C. These are independent raw analytic/data hypotheses, not own-paper operator conclusions or new Lean axioms. Theorem 1.1 retains its separately recorded older fixed-scale inputs and independent ordinary-square global decomposition; reflection is proved. Sparse applications additionally record OrdinarySquareStoppingInput CS and IndependentPrimeMaximalInput as explicit independent analytic boundaries. Their existence and the exact normalization/support/sign adaptations remain unproved; neither predicate contains this paper's endpoint or sparse conclusion.

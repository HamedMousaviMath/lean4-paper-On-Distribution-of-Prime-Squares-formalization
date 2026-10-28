# Checkpoint 849: Concrete cyclic square measures and exact Fourier coefficients

The finite cyclic low-model measure is now concrete: it is the pushforward of the character-weighted uniform measure on units under u -> u^2, normalized by phi(P). Lean proves its action on every test function, total variation at most one for every complex Dirichlet character, and exact equality of its finite Fourier coefficients with the existing twisted quadratic sums, with the manuscript's minus sign and totient normalization. The principal character gives the existing principal square sums. These identities remove an arithmetic identification premise at the full period; passage to a smaller denominator and conductor cancellation are subsequent work. No quantitative low maximal or prime-square restricted estimate is assumed or claimed.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| CyclicSquareMeasures.lean | 6 |

- `cyclicSquareMeasure_test`
- `cyclicVariation_nonneg`
- `cyclicSquareMeasure_variation_le_one`
- `cyclicFourier_norm_le_variation`
- `cyclicSquareMeasure_fourier`
- `cyclicPrincipalSquareMeasure_fourier`

<!-- checkpoint-verification -->

## Verification

All 916 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4535-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2504 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 918 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed source results under their paper hypotheses remain unchanged. Lemma 3.21, both conclusions of Theorems 1.1 and 1.3, all displayed clauses of Proposition 4.19 and both clauses of Proposition 6.21 are complete checked implications under their separately recorded independent deep inputs. The square-sign reflection is proved. Theorem 1.3 has actual finite sparse families, disjoint major subsets and the literal full all-cutoff maximum. The three general Section5 auxiliary statements remain partial, and the later Orlicz/ergodic/sieve applications remain unfinished. Proposition 4.19 consumes PrimeAsymptoticInputs, the refined PagePrimeSquareDistributionInputs c, RawPageUniquenessInput c and SmoothCircleBourgainInput C. These are independent raw analytic/data hypotheses, not own-paper operator conclusions or new Lean axioms. Theorem 1.1 retains its separately recorded older fixed-scale inputs and independent ordinary-square global decomposition; reflection is proved. Sparse applications additionally record OrdinarySquareStoppingInput CS and IndependentPrimeMaximalInput as explicit independent analytic boundaries. Their existence and the exact normalization/support/sign adaptations remain unproved; neither predicate contains this paper's endpoint or sparse conclusion. Section7 additionally records the independent RawTaoArcConstructionInput C, used only to obtain actual finite IW frequency geometry. Its existence is unproved; multiplier, sampling, low and high norm estimates are not fields and remain unfinished.

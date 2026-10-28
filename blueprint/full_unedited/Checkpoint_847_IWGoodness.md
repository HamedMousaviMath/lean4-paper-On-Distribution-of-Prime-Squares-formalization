# Checkpoint 847: Full quantitative Ionescu-Wainger goodness with an integer component maximum

The full Ionescu-Wainger goodness condition in Tao Definition1.3 (c=1/2) is now proved for the actual quantitative parameters. A natural integer maximum component is chosen without rounding the real component bound upwards; this avoids an erroneous factor exponential in r*k. The proof shows qmax^(2*r*k)<=B^(2*r) and the strict epsilon<1/(4*r*qmax^(2*r*k)) inequality, not just pairwise separation. Combined with the existing independent raw Tao construction, Lean now returns an actual finite frequency set with coverage, period, denominator cap and genuine goodness. The general multiplier/sampling and current-paper low/high estimates remain separate work and are not assumed here.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| IWGoodness.lean | 3 |

- `finite_component_maximum`
- `quantitative_iw_goodness`
- `quantitative_iw_construction_good`

<!-- checkpoint-verification -->

## Verification

All 914 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4521-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2484 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 916 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed source results under their paper hypotheses remain unchanged. Lemma 3.21, both conclusions of Theorems 1.1 and 1.3, all displayed clauses of Proposition 4.19 and both clauses of Proposition 6.21 are complete checked implications under their separately recorded independent deep inputs. The square-sign reflection is proved. Theorem 1.3 has actual finite sparse families, disjoint major subsets and the literal full all-cutoff maximum. The three general Section5 auxiliary statements remain partial, and the later Orlicz/ergodic/sieve applications remain unfinished. Proposition 4.19 consumes PrimeAsymptoticInputs, the refined PagePrimeSquareDistributionInputs c, RawPageUniquenessInput c and SmoothCircleBourgainInput C. These are independent raw analytic/data hypotheses, not own-paper operator conclusions or new Lean axioms. Theorem 1.1 retains its separately recorded older fixed-scale inputs and independent ordinary-square global decomposition; reflection is proved. Sparse applications additionally record OrdinarySquareStoppingInput CS and IndependentPrimeMaximalInput as explicit independent analytic boundaries. Their existence and the exact normalization/support/sign adaptations remain unproved; neither predicate contains this paper's endpoint or sparse conclusion. Section7 additionally records the independent RawTaoArcConstructionInput C, used only to obtain actual finite IW frequency geometry. Its existence is unproved; multiplier, sampling, low and high norm estimates are not fields and remain unfinished.

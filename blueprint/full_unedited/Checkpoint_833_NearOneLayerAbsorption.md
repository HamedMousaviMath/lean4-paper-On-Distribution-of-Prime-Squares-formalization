# Checkpoint 833: Global absorption of dyadic layer losses by the literal gauge

The dyadic layer-cake loss is absorbed into the literal gauge by proved uniform rescaling estimates. Lean proves coefficient monotonicity, rate(t)>=sqrt(log(exp(1)+t)), log(v)<=2sqrt(v) for v>=1, and a general variable-rescaling inequality when log(a)<=L+d rate(t). In particular a factor bounded by D log(exp(1)+t)^2 changes C to 9C+4 with an explicit constant depending only on C,D. This replaces the informal little-o sentence in the source by a global bound, including all bounded layers. The maximal operator restricted estimate is not assumed here, and its arithmetic derivation remains to be connected.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| NearOneLayerAbsorption.lean | 6 |

- `nearOneDensity_coefficient_mono`
- `nearOnePsi_coefficient_mono`
- `nearOneRate_ge_sqrt_log`
- `log_le_two_sqrt`
- `nearOnePsi_variable_rescale`
- `nearOnePsi_log_polynomial`

<!-- checkpoint-verification -->

## Verification

All 900 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4507-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2411 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 902 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed source results under their paper hypotheses remain unchanged. Lemma 3.21, both conclusions of Theorems 1.1 and 1.3, all displayed clauses of Proposition 4.19 and both clauses of Proposition 6.21 are complete checked implications under their separately recorded independent deep inputs. The square-sign reflection is proved. Theorem 1.3 has actual finite sparse families, disjoint major subsets and the literal full all-cutoff maximum. The three general Section5 auxiliary statements remain partial, and the later Orlicz/ergodic/sieve applications remain unfinished. Proposition 4.19 consumes PrimeAsymptoticInputs, the refined PagePrimeSquareDistributionInputs c, RawPageUniquenessInput c and SmoothCircleBourgainInput C. These are independent raw analytic/data hypotheses, not own-paper operator conclusions or new Lean axioms. Theorem 1.1 retains its separately recorded older fixed-scale inputs and independent ordinary-square global decomposition; reflection is proved. Sparse applications additionally record OrdinarySquareStoppingInput CS and IndependentPrimeMaximalInput as explicit independent analytic boundaries. Their existence and the exact normalization/support/sign adaptations remain unproved; neither predicate contains this paper's endpoint or sparse conclusion.

# Checkpoint 831: Quantitative Orlicz power absorption uniform near one

Lean proves the quantitative small-power absorption required near p=1. For every C>=1, 0<e<=1 and v>=1, C sqrt(v log(euler+v)) <= e v/2 + K(C)/e log(euler/e), where K(C)>0 is explicit and independent of e,v. Here euler means exp(1), while the variable e is p-1. The proof uses a logarithmic tangent inequality and a squared Young inequality, with no asymptotic implicit constants. Substituting the literal gauge logarithm gives density_C(t) <= exp(K(C)/e log(exp(1)/e)) (exp(1)+max(0,t))^(e/2) for every real t. This is the scalar dependence in c:orlicz-p; the operator distributional estimate and layer-cake integration are not assumed or claimed proved at this checkpoint.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| NearOneQuantitativeGrowth.lean | 5 |

- `nearOne_log_affine`
- `root_product_absorption`
- `nearOneGrowthConstant_pos`
- `nearOneCore_quantitative`
- `nearOneDensity_small_power`

<!-- checkpoint-verification -->

## Verification

All 898 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4505-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2396 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 900 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed source results under their paper hypotheses remain unchanged. Lemma 3.21, both conclusions of Theorems 1.1 and 1.3, all displayed clauses of Proposition 4.19 and both clauses of Proposition 6.21 are complete checked implications under their separately recorded independent deep inputs. The square-sign reflection is proved. Theorem 1.3 has actual finite sparse families, disjoint major subsets and the literal full all-cutoff maximum. The three general Section5 auxiliary statements remain partial, and the later Orlicz/ergodic/sieve applications remain unfinished. Proposition 4.19 consumes PrimeAsymptoticInputs, the refined PagePrimeSquareDistributionInputs c, RawPageUniquenessInput c and SmoothCircleBourgainInput C. These are independent raw analytic/data hypotheses, not own-paper operator conclusions or new Lean axioms. Theorem 1.1 retains its separately recorded older fixed-scale inputs and independent ordinary-square global decomposition; reflection is proved. Sparse applications additionally record OrdinarySquareStoppingInput CS and IndependentPrimeMaximalInput as explicit independent analytic boundaries. Their existence and the exact normalization/support/sign adaptations remain unproved; neither predicate contains this paper's endpoint or sparse conclusion.

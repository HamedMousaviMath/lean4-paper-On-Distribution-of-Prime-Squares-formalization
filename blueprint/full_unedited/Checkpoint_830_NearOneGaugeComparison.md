# Checkpoint 830: Orlicz gauge comparison and doubling with explicit constants

The matching lower comparison and doubling of the literal Section7 gauge are now proved. A direct algebraic logarithmic tangent estimate proves sqrt(y log(e+y)) <= sqrt(x log(e+x))+2(y-x) for 1<=x<=y. Consequently the actual density satisfies the fixed-rescaling bound exp(2 C log a) for every a>=1. Integration over the final half interval gives the lower gauge comparison, and together with the upper comparison proves the displayed asymptotic equivalence in e:orlicz-gauge-comparison with explicit constants and a doubling inequality. These are unconditional scalar and integration deductions. No IW, maximal, modular or ergodic bound is assumed or claimed here.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| NearOneGaugeComparison.lean | 7 |

- `nearOne_innerLog_bounds`
- `nearOneCore_lipschitz`
- `nearOneRate_rescale`
- `nearOneDensity_rescale`
- `nearOnePsi_ge_half_density`
- `nearOnePsi_comparison`
- `nearOnePsi_doubling`

<!-- checkpoint-verification -->

## Verification

All 897 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4504-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2391 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 899 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed source results under their paper hypotheses remain unchanged. Lemma 3.21, both conclusions of Theorems 1.1 and 1.3, all displayed clauses of Proposition 4.19 and both clauses of Proposition 6.21 are complete checked implications under their separately recorded independent deep inputs. The square-sign reflection is proved. Theorem 1.3 has actual finite sparse families, disjoint major subsets and the literal full all-cutoff maximum. The three general Section5 auxiliary statements remain partial, and the later Orlicz/ergodic/sieve applications remain unfinished. Proposition 4.19 consumes PrimeAsymptoticInputs, the refined PagePrimeSquareDistributionInputs c, RawPageUniquenessInput c and SmoothCircleBourgainInput C. These are independent raw analytic/data hypotheses, not own-paper operator conclusions or new Lean axioms. Theorem 1.1 retains its separately recorded older fixed-scale inputs and independent ordinary-square global decomposition; reflection is proved. Sparse applications additionally record OrdinarySquareStoppingInput CS and IndependentPrimeMaximalInput as explicit independent analytic boundaries. Their existence and the exact normalization/support/sign adaptations remain unproved; neither predicate contains this paper's endpoint or sparse conclusion.

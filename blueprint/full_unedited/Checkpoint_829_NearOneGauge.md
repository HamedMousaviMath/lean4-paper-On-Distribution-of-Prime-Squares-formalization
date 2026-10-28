# Checkpoint 829: Literal Section7 Orlicz gauge and convexity

The literal Section7 integrand and its primitive Psi_C are defined. A continuous clamp extends the density to negative arguments and is proved identical to the printed formula for every nonnegative argument. Lean proves positivity, monotonicity and continuity of the density; the fundamental theorem of calculus for Psi_C; its continuity, monotonicity and convexity; Psi_C(0)=0; Psi_C(t)>=t for C>=0,t>=0; and the upper comparison Psi_C(t)<=t exp(C rate(t)). No analytic theorem is assumed. The matching lower comparison, doubling, quantitative optimization and all operator conclusions remain to be developed. This checkpoint does not close Theorem t:orlicz-maximal (archived number7.2) or either ergodic corollary.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| NearOneGauge.lean | 17 |

- `nearOneLog_one_le`
- `nearOneLog_mono`
- `nearOneRate_nonneg`
- `nearOneRate_mono`
- `nearOneDensity_continuous`
- `nearOneDensity_pos`
- `nearOneDensity_one_le`
- `nearOneDensity_mono`
- `nearOnePsi_zero`
- `nearOnePsi_nonneg`
- `nearOnePsi_hasDerivAt`
- `nearOnePsi_continuous`
- `nearOnePsi_mono`
- `nearOnePsi_convex`
- `nearOnePsi_ge_self`
- `nearOnePsi_le_density`
- `nearOneGauge_literal`

<!-- checkpoint-verification -->

## Verification

All 896 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4503-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2384 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 898 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed source results under their paper hypotheses remain unchanged. Lemma 3.21, both conclusions of Theorems 1.1 and 1.3, all displayed clauses of Proposition 4.19 and both clauses of Proposition 6.21 are complete checked implications under their separately recorded independent deep inputs. The square-sign reflection is proved. Theorem 1.3 has actual finite sparse families, disjoint major subsets and the literal full all-cutoff maximum. The three general Section5 auxiliary statements remain partial, and the later Orlicz/ergodic/sieve applications remain unfinished. Proposition 4.19 consumes PrimeAsymptoticInputs, the refined PagePrimeSquareDistributionInputs c, RawPageUniquenessInput c and SmoothCircleBourgainInput C. These are independent raw analytic/data hypotheses, not own-paper operator conclusions or new Lean axioms. Theorem 1.1 retains its separately recorded older fixed-scale inputs and independent ordinary-square global decomposition; reflection is proved. Sparse applications additionally record OrdinarySquareStoppingInput CS and IndependentPrimeMaximalInput as explicit independent analytic boundaries. Their existence and the exact normalization/support/sign adaptations remain unproved; neither predicate contains this paper's endpoint or sparse conclusion.

# Checkpoint 102: A proved rational selection at balanced precision

Mathlib's proved Dirichlet approximation theorem is applied with the integer cutoff floor(x^(3/2)). For every x>=1 and every real xi, Lean constructs a reduced rational r with den(r)<=x^(3/2), |xi-r|<=1/(den(r)*x^(3/2)), and the strict bound |xi-r|<1/den(r)^2. Floor errors, positive denominators and the cutoff's positivity are proved explicitly. This applies to rational and irrational xi alike.

The annular specialization sets x=N/2 for natural N>=2. If xi lies in [0,1], the selected rational lies in [-1,2]. No rational approximation is supplied as an unproved existence assumption. The strict reciprocal-square bound is the compatibility needed for the external Ghosh estimate; the finer x^(-3/2) precision also controls Ren's effective denominator in the smaller-denominator branch.

This is a new approximation used by the complementary argument; it need not be the manuscript's original approximant. No change to the manuscript is prescribed. The prime exponential-sum estimates remain explicit deep-input hypotheses.


## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| BalancedRationalApproximation.lean | 3 |

- `exists_balanced_rational_approximation`
- `exists_balanced_annular_approximation`
- `balanced_approximation_representative_range`

<!-- checkpoint-verification -->

## Verification

All 169 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 3691-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 988 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 171 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. Published Ren and Ghosh quadratic exponential-sum estimates, when consumed, remain displayed raw theorem hypotheses; the progression-prefix estimate also remains an explicit unproved input. No own-paper analytic conclusion is assumed.

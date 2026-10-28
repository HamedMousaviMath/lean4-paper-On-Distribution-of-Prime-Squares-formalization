# Checkpoint 101: Effective-denominator bounds for the balanced approximation

This checkpoint proves the elementary geometry for a new balanced rational approximation. If x>0, 0<q<=sqrt(x), and the real offset satisfies |theta|<=1/(q*x^(3/2)), then Ren's effective denominator T=q*(1+|theta|*x^2) lies between q and 2*sqrt(x). The upper bound is exact and uses the real-power identity x^2=x^(3/2)*x^(1/2).

A complementary lower bound is proved: T>=R/4 whenever either q>=R or |theta|>=R/(4*q*x^2), for x>0 and R>=0. With N=2*x, the latter threshold is exactly the width R/(q*N^2) of a source major arc. Thus being outside the small-denominator arcs will force T large, even when the newly selected q itself is small.

These statements are inequalities for the actual previously defined renEffectiveDenominator, not assumptions about an abstract replacement. They use no exponential-sum or distribution theorem. Selecting a compatible rational approximation and connecting the outside-arc condition are separate subsequent tasks.


## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| BalancedEffectiveDenominator.lean | 3 |

- `renEffectiveDenominator_ge`
- `renEffectiveDenominator_balanced_upper`
- `renEffectiveDenominator_lower_from_arc`

<!-- checkpoint-verification -->

## Verification

All 168 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 3687-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 985 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 170 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. Published Ren and Ghosh quadratic exponential-sum estimates, when consumed, remain displayed raw theorem hypotheses; the progression-prefix estimate also remains an explicit unproved input. No own-paper analytic conclusion is assumed.

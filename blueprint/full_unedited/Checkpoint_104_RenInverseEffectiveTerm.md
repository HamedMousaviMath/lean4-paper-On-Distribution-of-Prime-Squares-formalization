# Checkpoint 104: The inverse effective-denominator term with divisor loss retained

The inverse-effective-denominator term is controlled with the divisor loss included. If q>=0, R>0, q<=T and R/4<=T, then

    q^(1/12)/sqrt(T) <= 4^(5/12)*R^(-5/12).

The proof first replaces q^(1/12) by T^(1/12), giving T^(-5/12), and then uses the lower bound on T. This avoids inserting an uncontrolled q^epsilon factor into an R-only estimate. The exact normalized third term q^(1/12)*(x/sqrt(T))/x satisfies the same bound for x>0; its cancellation is justified.

These are unconditional real inequalities. In the later application, the new approximation gives the upper bound on T and the outside-major-arc condition gives the lower bound. No bound on a prime sum is inferred until its explicit Ren hypothesis has been supplied.


## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| RenInverseEffectiveTerm.lean | 2 |

- `weighted_inverse_sqrt_effective`
- `ren_third_weighted_term`

<!-- checkpoint-verification -->

## Verification

All 171 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 3693-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 995 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 173 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. Published Ren and Ghosh quadratic exponential-sum estimates, when consumed, remain displayed raw theorem hypotheses; the progression-prefix estimate also remains an explicit unproved input. No own-paper analytic conclusion is assumed.

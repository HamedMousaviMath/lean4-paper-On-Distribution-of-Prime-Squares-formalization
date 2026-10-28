# Checkpoint 105: The complete weighted Ren bracket in the balanced regime

The three previously proved weighted term bounds are combined into the explicit renBalancedBudget(x,R): sqrt(2)*x^(-5/24)+x^(-19/120)+4^(5/12)*R^(-5/12). Its nonnegativity is proved on nonnegative bases.

For positive x,R, 0<=q<=sqrt(x), q<=T<=2*sqrt(x), and T>=R/4, Lean proves q^(1/12)*renQuadraticBracket(x,T)/x<=renBalancedBudget(x,R). A second theorem substitutes the actual effective denominator associated to an approximation satisfying |theta|<=1/(q*x^(3/2)). The upper bound and q<=T then come from the checked geometry, rather than extra analytic assumptions.

This is an unconditional recombination of inequalities. The next consuming theorem inserts the raw Ren exponential-sum estimate and its genuine divisor prefactor; no prime-sum bound is assumed or asserted in the present statements.


## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| RenBalancedBracket.lean | 3 |

- `renBalancedBudget_nonneg`
- `ren_weighted_bracket_balanced`
- `ren_weighted_bracket_from_balanced_approximation`

<!-- checkpoint-verification -->

## Verification

All 172 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 3694-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 998 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 174 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. Published Ren and Ghosh quadratic exponential-sum estimates, when consumed, remain displayed raw theorem hypotheses; the progression-prefix estimate also remains an explicit unproved input. No own-paper analytic conclusion is assumed.

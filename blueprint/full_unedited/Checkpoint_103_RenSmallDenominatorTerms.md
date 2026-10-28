# Checkpoint 103: The first two normalized Ren terms with the divisor loss retained

The first two terms of Ren's three-term bracket are bounded while retaining the q^(1/12) loss proved necessary for its divisor prefactor. For x>0 and 0<=q<=sqrt(x), Lean proves q^(1/12)<=x^(1/24). If the effective denominator T<=2*sqrt(x), then sqrt(T)<=sqrt(2)*x^(1/4).

These yield the exact normalized inequalities

    q^(1/12)*sqrt(x)*sqrt(T)/x <= sqrt(2)*x^(-5/24),
    q^(1/12)*x^(4/5)/x <= x^(-19/120).

All real-power identities, positivity conditions and normalization by x are checked in Lean. The denominator q is a real parameter in these inequalities, allowing the later natural denominator to be substituted without changing the statement. No external analytic estimate is assumed. The remaining inverse-effective-denominator term is handled separately before the bracket is recombined.


## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| RenSmallDenominatorTerms.lean | 5 |

- `rpow_product_div_self`
- `smallDenominator_twelfth`
- `effectiveDenominator_sqrt_bound`
- `ren_first_weighted_term`
- `ren_middle_weighted_term`

<!-- checkpoint-verification -->

## Verification

All 170 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 3692-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 993 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 172 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. Published Ren and Ghosh quadratic exponential-sum estimates, when consumed, remain displayed raw theorem hypotheses; the progression-prefix estimate also remains an explicit unproved input. No own-paper analytic conclusion is assumed.

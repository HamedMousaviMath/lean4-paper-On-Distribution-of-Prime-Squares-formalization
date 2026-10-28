# Checkpoint 123: Exact dyadic logarithms and inverse-power comparison

Lean records the exact arithmetic and logarithmic identities for dyadic scales 2^j. In particular log(2^j)=j*log 2 and monotonicity in the exponent is proved.

Since 0<log 2<=1, the bound log 2*(j+1)<=1+log(2^j) holds even at j=0. For every A>=0 this gives

    (1+log(2^j))^(-A) <= (log 2)^(-A)*(j+1)^(-A).

The explicit constant will convert the conditional global operator-error bound to a summable sequence in the dyadic exponent. No asymptotic substitution of j for log N is left informal.


## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| DyadicLogarithmicBudget.lean | 4 |

- `two_pow_monotone`
- `log_two_pow_nat`
- `dyadic_log_linear_lower`
- `dyadic_log_inverse_power`

<!-- checkpoint-verification -->

## Verification

All 190 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 3712-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 1045 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 192 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. Published Ren and Ghosh quadratic exponential-sum estimates, when consumed, remain displayed raw theorem hypotheses; the progression-prefix estimate also remains an explicit unproved input. No own-paper analytic conclusion is assumed.

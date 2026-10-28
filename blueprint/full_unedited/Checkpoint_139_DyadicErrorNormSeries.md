# Checkpoint 139: Absolute norm summability of the actual dyadic error family

The actual dyadic circle-error family is proved absolutely summable in operator norm on every allowed tail. For a fixed exponent s>=2, the previously established decay and upward Q-range condition give

    sum_j norm(E_(2^(J+j))) <= 2*dyadicErrorConstant(s)*Q^(-1/2)*(J+1)^(1-s).

Both summability and the explicit bound are proved. The arithmetic threshold is chosen before J, Q, the input and all scale-dependent character, coefficient and beta data. CircleAnalyticInputs is required at the actual scales in the tail, with uniform displayed deep-input constants.

This supplies a genuine summable family for the countable maximal construction. No maximal-error inequality is assumed in the input.


## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| DyadicErrorNormSeries.lean | 1 |

- `dyadicCircleError_norm_series`

<!-- checkpoint-verification -->

## Verification

All 206 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 3731-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 1086 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 208 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. Published Ren and Ghosh quadratic exponential-sum estimates, when consumed, remain displayed raw theorem hypotheses; the progression-prefix estimate also remains an explicit unproved input. No own-paper analytic conclusion is assumed.

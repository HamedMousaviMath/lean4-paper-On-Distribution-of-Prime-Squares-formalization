# Checkpoint 114: Absorbing fixed logarithmic and power budgets

Lean proves that every fixed real power of log R is eventually bounded by R^epsilon for any fixed epsilon>0. The proof consumes a proved Mathlib little-o limit and retains explicit positivity before simplifying norms. It does not use a number-theoretic asymptotic assumption.

Two constant-absorption statements are also proved. If K>=0 and a<b, then K*R^a<=R^b eventually; and if two nonnegative weighted powers both have exponent below b, their sum is eventually at most R^b. The finite constants are absorbed into thresholds, never by changing exponents with R.

These supporting inequalities will absorb the genuine logarithmic factor in the complementary minor budget. They do not by themselves assert an estimate for a prime exponential sum.


## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| LogPowerAbsorption.lean | 3 |

- `eventually_log_rpow_le_rpow`
- `eventually_scaled_rpow_le_rpow`
- `eventually_two_rpow_budget`

<!-- checkpoint-verification -->

## Verification

All 181 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 3703-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 1022 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 183 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. Published Ren and Ghosh quadratic exponential-sum estimates, when consumed, remain displayed raw theorem hypotheses; the progression-prefix estimate also remains an explicit unproved input. No own-paper analytic conclusion is assumed.

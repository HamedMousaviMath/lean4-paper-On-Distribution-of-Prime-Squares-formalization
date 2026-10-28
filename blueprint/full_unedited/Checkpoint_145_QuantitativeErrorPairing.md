# Checkpoint 145: Finite-indicator pairing bounds for the conditional error operator

An actual l2 operator norm bound gives an explicit finite-indicator pairing bound b*sqrt(|F|)*sqrt(|G|), without kernel positivity. Lean proves this using the existing finite-indicator norm and discrete Cauchy--Schwarz estimate. Its normalized form is b*(|F||G|/L^2)^(1/2) after division by a positive spatial length L.

The conditional global circle-error norm theorem is then applied to obtain this finite-set error bound uniformly in the permitted Q and actual analytic inputs. The result is the quantitative error pairing needed in later restricted improving arguments.

This controls the error contribution only. The low and high contributions needed for Theorem 1.1 have not been supplied, so no full improving theorem is claimed.


## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| QuantitativeErrorPairing.lean | 3 |

- `operator_finite_indicator_pairing_bound`
- `operator_finite_indicator_pairing_normalized`
- `globalCircleError_restricted_bound`

<!-- checkpoint-verification -->

## Verification

All 212 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 3737-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 1101 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 214 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. Published Ren and Ghosh quadratic exponential-sum estimates, when consumed, remain displayed raw theorem hypotheses; the progression-prefix estimate also remains an explicit unproved input. No own-paper analytic conclusion is assumed.

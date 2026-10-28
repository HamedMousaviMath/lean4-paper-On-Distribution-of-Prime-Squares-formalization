# Checkpoint 124: Quantitative decay of the actual dyadic error operators

An actual dyadic family of l2 error operators is defined from the genuine periodized circle model, with character, coefficient and beta data allowed to vary with the dyadic exponent. One positive constant dyadicErrorConstant(A)=2*2^A*(log 2)^(-A) is selected explicitly.

The global conditional l2 approximation, the upward stability of the allowed Q range and the dyadic logarithmic comparison prove an operator norm bound

    norm(E_(2^j)) <= dyadicErrorConstant(A)*Q^(-1/2)*(j+1)^(-A)

for every j beyond a chosen starting exponent, under the explicit analytic inputs at those scales. A single arithmetic threshold is chosen before the starting exponent, Q and all scale-dependent data. The Q restriction is required only at the starting scale and is then proved at later scales.

These are genuine bounded operators acting on every l2 input. The external progression, Ren and Ghosh inputs remain explicit via CircleAnalyticInputs; no maximal-error or high/low conclusion is assumed.


## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| DyadicCircleErrorBudget.lean | 2 |

- `dyadicErrorConstant_pos`
- `dyadicCircleError_operator_decay`

<!-- checkpoint-verification -->

## Verification

All 191 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 3713-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 1047 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 193 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. Published Ren and Ghosh quadratic exponential-sum estimates, when consumed, remain displayed raw theorem hypotheses; the progression-prefix estimate also remains an explicit unproved input. No own-paper analytic conclusion is assumed.

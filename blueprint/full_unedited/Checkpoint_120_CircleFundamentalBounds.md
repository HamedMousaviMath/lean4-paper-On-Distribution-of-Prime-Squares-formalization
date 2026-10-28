# Checkpoint 120: From a fundamental representative interval to all circle points

Every point of PrimeCircle is represented by a real xi in the half-open interval [0,1), using Mathlib's proved quotient equivalence. Consequently a bound for a continuous circle function on the closed representative interval [0,1] is a bound at every circle point. Endpoints are included consistently.

The same fundamental-interval bound controls the norm of the actual integer l2 multiplier operator through the previously proved negative-phase Fourier isometry. The function is an actual continuous circle symbol and the operator acts on all l2 inputs; no finite-input or formal-symbol substitute is used.

These quotient and operator-transfer facts introduce no analytic hypothesis or new mathematical axiom. They allow the newly proved conditional global error bound to yield an actual all-input operator estimate.


## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| CircleFundamentalBounds.lean | 3 |

- `primeCircle_representative`
- `circleBound_from_fundamental_interval`
- `integerMultiplier_bound_fundamental_interval`

<!-- checkpoint-verification -->

## Verification

All 187 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 3709-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 1036 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 189 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. Published Ren and Ghosh quadratic exponential-sum estimates, when consumed, remain displayed raw theorem hypotheses; the progression-prefix estimate also remains an explicit unproved input. No own-paper analytic conclusion is assumed.

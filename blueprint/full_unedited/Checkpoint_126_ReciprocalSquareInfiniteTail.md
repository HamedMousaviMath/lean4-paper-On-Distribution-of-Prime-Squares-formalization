# Checkpoint 126: A quantitative infinite reciprocal-square tail

Finite sums indexed by a shifted range are identified exactly with sums on [J,J+K). The reciprocal-square finite-tail bound then bounds every partial sum of the shifted nonnegative series.

Lean proves both summability of the series sum_j 1/(J+j+1)^2 and the explicit bound 2/(J+1). The proof works for every natural J, including J=0. It uses the proved nonnegative-series criterion and the finite telescoping estimate; no numerical approximation or assumed zeta value is involved.

This prepares a quantitative infinite envelope for the actual dyadic operator errors.


## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| ReciprocalSquareInfiniteTail.lean | 3 |

- `sum_range_shift_eq_Ico`
- `reciprocal_square_shift_summable`
- `reciprocal_square_infinite_tail`

<!-- checkpoint-verification -->

## Verification

All 193 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 3718-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 1053 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 195 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. Published Ren and Ghosh quadratic exponential-sum estimates, when consumed, remain displayed raw theorem hypotheses; the progression-prefix estimate also remains an explicit unproved input. No own-paper analytic conclusion is assumed.

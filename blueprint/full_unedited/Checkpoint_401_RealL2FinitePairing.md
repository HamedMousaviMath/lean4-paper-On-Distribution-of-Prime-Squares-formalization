# Checkpoint 401: The finite test-set bound for a nonnegative genuine real l2 majorant

Cauchy-Schwarz and the actual lp square-energy formula give sum_G g<=||g||_2 sqrt(|G|) for nonnegative real l2 functions. A complex function dominated by g inherits the same finite sum bound.


## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| RealL2FinitePairing.lean | 2 |

- `real_l2_finite_sum_bound`
- `real_l2_majorant_finite_sum`

<!-- checkpoint-verification -->

## Verification

All 468 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4075-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 1583 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 470 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. Published Ren and Ghosh quadratic exponential-sum estimates, when consumed, remain displayed raw theorem hypotheses; the progression-prefix estimate also remains an explicit unproved input. No own-paper analytic conclusion is assumed.

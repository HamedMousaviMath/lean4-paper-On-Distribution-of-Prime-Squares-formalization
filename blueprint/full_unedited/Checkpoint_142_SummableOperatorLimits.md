# Checkpoint 142: Vanishing outputs of norm-summable operator families

A norm-summable family of bounded l2 operators produces an absolutely summable output series for every complex l2 input. Lean proves that the individual outputs tend to zero in l2 and at every integer coordinate.

The pointwise statement uses the continuity of coordinate evaluation on l2, so it does not rely on selecting an almost-everywhere subsequence. Applied to the norm-summable actual dyadic error tail, it shows that model approximation errors vanish along that full tail under the recorded analytic inputs.

These are consequences of the already checked summability mechanism; they are not claims of the paper's ergodic convergence theorem.


## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| SummableOperatorLimits.lean | 3 |

- `operator_outputs_summable`
- `operator_outputs_tendsto_zero_l2`
- `operator_outputs_tendsto_zero_pointwise`

<!-- checkpoint-verification -->

## Verification

All 209 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 3734-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 1093 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 211 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. Published Ren and Ghosh quadratic exponential-sum estimates, when consumed, remain displayed raw theorem hypotheses; the progression-prefix estimate also remains an explicit unproved input. No own-paper analytic conclusion is assumed.

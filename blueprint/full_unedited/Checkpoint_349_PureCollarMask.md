# Checkpoint 349: The actual complementary narrow cutoff and its exact range

The pure collar mask 1-eta(q N^2 theta/Q) lies in [0,1], vanishes at theta=0, and agrees exactly with the earlier high mask whenever q<=Q. The pure mask is useful even for arbitrary positive effective cutoffs.


## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| PureCollarMask.lean | 3 |

- `annularCollarMask_range`
- `annularCollarMask_at_zero`
- `annularHighMask_eq_collar`

<!-- checkpoint-verification -->

## Verification

All 416 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4023-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 1511 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 418 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. Published Ren and Ghosh quadratic exponential-sum estimates, when consumed, remain displayed raw theorem hypotheses; the progression-prefix estimate also remains an explicit unproved input. No own-paper analytic conclusion is assumed.

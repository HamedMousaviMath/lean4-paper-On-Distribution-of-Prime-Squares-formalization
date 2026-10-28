# Checkpoint 86: The extra broad cutoff is redundant under the exceptional width condition

The same redundancy is proved for the exact exceptional narrow cutoff, with positive Q, B0 and q0 and the explicit effective-width condition Q*q0/B0<=R. Its dilation is first identified algebraically with qN^2/(Q*q0/B0), then the proved geometric containment applies. The effective-width condition is displayed rather than silently assumed to follow from conductor data; connecting the full source range to this condition remains an arithmetic parameter obligation.


## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| ExceptionalLowContainment.lean | 1 |

- `exceptionalNarrowCutoff_mul_broad`

<!-- checkpoint-verification -->

## Verification

All 153 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 3672-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 932 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 155 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. The already displayed raw progression-prefix estimate is consumed as a theorem hypothesis; it remains unproved. No new external analytic estimate or own-paper lemma is assumed.

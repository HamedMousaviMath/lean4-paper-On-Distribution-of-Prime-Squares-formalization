# Checkpoint 72: The narrow cutoff lies inside the broad cutoff core

Under the proved geometric budget 2R^4<=N^2, with q<=R, Q<=R and the appropriate dyadic index, every nonzero narrow cutoff eta((qN^2/Q)theta) lies inside the region where the broad dyadic cutoff is exactly one. Hence multiplying the narrow cutoff by the broad cutoff leaves it unchanged. This is an exact support-containment identity and is needed to justify compactifying the low model without altering it in the admissible range.


## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| NarrowCutoffContainment.lean | 2 |

- `narrowCutoff_inside_broad_core`
- `narrowCutoff_mul_broad`

<!-- checkpoint-verification -->

## Verification

All 139 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 3658-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 909 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 141 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. The already displayed raw progression-prefix estimate is consumed as a theorem hypothesis; it remains unproved. No new external analytic estimate or own-paper lemma is assumed.

# Checkpoint 89: A genuine nonnegative l2 envelope for finite operator families

For a finite family of genuine l2 operators, the pointwise magnitudes of their outputs are assembled into an actual nonnegative real l2 envelope. Taking pointwise magnitude preserves the l2 norm exactly, and the finite envelope dominates the output magnitude of every member of the family at every integer. This prepares a rigorously defined maximal majorant; it does not claim a uniform infinite-scale maximal theorem.


## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| FiniteOperatorEnvelope.lean | 3 |

- `magnitudeL2_norm`
- `finiteOperatorEnvelope_nonneg`
- `finiteOperatorEnvelope_dominates`

<!-- checkpoint-verification -->

## Verification

All 156 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 3675-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 937 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 158 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. The already displayed raw progression-prefix estimate is consumed as a theorem hypothesis; it remains unproved. No new external analytic estimate or own-paper lemma is assumed.

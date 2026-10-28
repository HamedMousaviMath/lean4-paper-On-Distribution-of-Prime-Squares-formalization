# Checkpoint 90: Finite-family l2 maximal control through the explicit envelope

The finite l2 envelope has norm at most the sum of the individual operator bounds times the input norm. Every nonnegative pointwise function dominated by this envelope is proved to belong to real l2 with the same bound. In particular, this supplies the finite-family maximal bound once a pointwise maximum is dominated by the envelope. The bound depends on the sum of scale bounds; proving the source's uniform infinite-family or multifrequency maximal estimate remains open.


## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| FiniteMaximalEnvelopeBound.lean | 2 |

- `finiteOperatorEnvelope_norm`
- `finiteOperator_dominated_maximal`

<!-- checkpoint-verification -->

## Verification

All 157 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 3676-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 939 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 159 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. The already displayed raw progression-prefix estimate is consumed as a theorem hypothesis; it remains unproved. No new external analytic estimate or own-paper lemma is assumed.

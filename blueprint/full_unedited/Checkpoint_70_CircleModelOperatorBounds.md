# Checkpoint 70: All-input l2 and l1-to-linfinity bounds for the finite circle model

The explicit finite-center Gauss bound now controls both the actual l2 model operator and its compatible l1-to-linfinity realization. The first uses Plancherel and the global circle-symbol bound; the second uses the actual inverse-kernel bound. Both hold for every input in the corresponding Banach space and use the same finite center set and exceptional data. The estimate is a coarse finite-model bound, not the source-specific improved low or high estimate.


## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| CircleModelOperatorBounds.lean | 2 |

- `circleMajorArcOperator_bound`
- `circleMajorArcL1Operator_bound`

<!-- checkpoint-verification -->

## Verification

All 137 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 3656-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 905 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 139 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. The already displayed raw progression-prefix estimate is consumed as a theorem hypothesis; it remains unproved. No new external analytic estimate or own-paper lemma is assumed.

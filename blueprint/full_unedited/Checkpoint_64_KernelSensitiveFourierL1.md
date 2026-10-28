# Checkpoint 64: Operator estimates from sharper inverse-kernel bounds

The l1-to-linfinity operator is bounded by any valid pointwise bound on its inverse kernel, even when that bound is smaller than the symbol sup norm used to construct the operator. Both the all-input norm estimate and the operator-norm estimate are proved. This distinction is useful for the source's low term, where arithmetic cancellation in the inverse kernel must provide a sharper bound than the immediate symbol estimate. No such arithmetic cancellation is assumed or claimed in this checkpoint.


## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| KernelSensitiveFourierL1.lean | 2 |

- `fourierL1Operator_kernel_bound`
- `fourierL1Operator_opNorm_kernel_bound`

<!-- checkpoint-verification -->

## Verification

All 131 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 3650-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 892 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 133 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. The already displayed raw progression-prefix estimate is consumed as a theorem hypothesis; it remains unproved. No new external analytic estimate or own-paper lemma is assumed.

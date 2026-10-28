# Checkpoint 68: Spatial model and error bounds from the genuine circle symbols

The global finite model's actual inverse kernel satisfies the explicit denominator-weighted Gauss bound at every spatial integer. Any uniform circle error bound also bounds the actual error kernel pointwise. These are proved through the Fourier coefficient integral and the already checked circle-model estimates. The second statement is transport of a displayed hypothesis; it does not discharge the missing global minor-arc estimate.


## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| CircleModelKernelBounds.lean | 2 |

- `circleModelKernel_bound`
- `circleModelErrorKernel_bound`

<!-- checkpoint-verification -->

## Verification

All 135 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 3654-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 901 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 137 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. The already displayed raw progression-prefix estimate is consumed as a theorem hypothesis; it remains unproved. No new external analytic estimate or own-paper lemma is assumed.

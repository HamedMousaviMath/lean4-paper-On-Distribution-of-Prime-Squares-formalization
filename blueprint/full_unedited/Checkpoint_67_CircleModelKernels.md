# Checkpoint 67: Actual model and error kernels with exact annular decomposition

The actual global finite circle model and its error now have inverse Fourier kernels. The model kernel is proved to be the finite sum of the periodized rational-term kernels. At every integer, the genuine annular von-Mangoldt square kernel equals the model kernel plus the error kernel, using the already checked Fourier identification of the actual averaging kernel. No finite spatial support is asserted for the two new kernels.


## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| CircleModelKernels.lean | 2 |

- `circleModelKernel_sum`
- `annularKernel_circle_decomposition`

<!-- checkpoint-verification -->

## Verification

All 134 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 3653-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 899 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 136 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. The already displayed raw progression-prefix estimate is consumed as a theorem hypothesis; it remains unproved. No new external analytic estimate or own-paper lemma is assumed.

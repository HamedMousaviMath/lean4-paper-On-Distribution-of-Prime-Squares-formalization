# Checkpoint 69: Exact finite-input convolution formulas for model and error operators

The genuine l2 model and error operators are proved to act on every finite complex input by convolution with their actual inverse Fourier kernels. This identifies the spatial and frequency constructions for both components, preserving the input support and the sign convention. The exact annular kernel decomposition is already available; no extra positivity or spatial support of model kernels is assumed.


## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| CircleModelConvolution.lean | 2 |

- `circleModelOperator_finite_convolution`
- `circleModelErrorOperator_finite_convolution`

<!-- checkpoint-verification -->

## Verification

All 136 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 3655-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 903 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 138 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. The already displayed raw progression-prefix estimate is consumed as a theorem hypothesis; it remains unproved. No new external analytic estimate or own-paper lemma is assumed.

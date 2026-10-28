# Checkpoint 58: Uniform inverse-kernel and finite-input convolution estimates

Every continuous circle symbol with a uniform pointwise bound B has an inverse Fourier kernel bounded by B at every integer. The proof uses the actual Fourier coefficient integral, the unit norm of the Fourier character and the normalized Haar mass one. This gives an explicit finite-input convolution bound B times the sum of input magnitudes, valid without positivity or compact spatial support. These facts supply the basic l1-to-linfinity kernel estimate needed for low operators; the source's stronger low estimate is not claimed.


## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| UniformFourierKernel.lean | 2 |

- `fourierKernel_uniform_bound`
- `fourierKernel_finite_input_bound`

<!-- checkpoint-verification -->

## Verification

All 125 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 3644-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 880 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 127 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. The already displayed raw progression-prefix estimate is consumed as a theorem hypothesis; it remains unproved. No new external analytic estimate or own-paper lemma is assumed.

# Checkpoint 1177: Scaled cutoff support and square positivity

Positive Euclidean dilation of a Fourier multiplier has its genuine inverse transform equal to the dilated inverse transform times the positive reciprocal scale. This proves inverse-transform positivity for the actual scaled eta_N, not a newly assumed kernel.

For every Schwartz multiplier with real nonnegative inverse transform, the inverse transform of its square is proved equal to the genuine convolution of its inverse transforms, and is real nonnegative. This applies to the exact eta_N squared in the manuscript.

The seed support inside (-1/8,1/8) gives eta=0 whenever |x|≥1/4. The scaled cutoff therefore vanishes whenever |gamma|≥R/(4N²). All conclusions use ordinary Mathlib Fourier inversion and actual integrals. The full singular-integral positivity and smoothing estimate and the major-completion lemma are not yet claimed.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachScaledCutoff.lean | 5 |

- `goldbach_inverse_fourier_scale`
- `goldbach_scaled_eta_inverse_nonnegative`
- `goldbach_cutoff_square_inverse_nonnegative`
- `goldbach_eta_support`
- `goldbach_scaled_eta_support`

<!-- checkpoint-verification -->

## Verification

All 1244 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 5037-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 3931 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1246 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; the Section10/11 analytic and sieve estimates remain open internal obligations. The rational smooth multifrequency theorem with circle transference remains an explicit independent compound hypothesis. The classical primitive sum-of-two-squares criterion is an additional explicit independent arithmetic hypothesis for Section9 reductions; it contains no own-paper conclusion and is not declared as a Lean axiom.

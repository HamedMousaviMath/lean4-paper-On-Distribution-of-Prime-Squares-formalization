# Checkpoint 1176: Actual autocorrelation cutoff and inverse Fourier positivity

The paper allows an arbitrary nonzero real smooth compactly supported seed; it does not assume that the seed itself is even or nonnegative. The formal construction now complexifies any real Schwartz seed, reflects it, and takes its genuine convolution. The convolution is proved equal to the actual real autocorrelation integral. Its value at zero is the integral of the seed squared, proved strictly positive from nonzeroness and continuity.

The Fourier transform of the reflection is the conjugate transform of the seed. Consequently the autocorrelation transform is the squared complex modulus. Normalization gives eta(0)=1, and its actual Euclidean inverse Fourier transform is real and nonnegative. These are proved facts, not additional assumptions about the paper kernel. Scaling, support and quantitative smoothing, the singular integral and major completion remain to be assembled.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachAutocorrelation.lean | 8 |

- `goldbach_autocorrelation_integral`
- `goldbach_seed_mass_pos`
- `goldbach_autocorrelation_zero`
- `goldbach_real_seed_fourier_conj`
- `goldbach_reflected_seed_fourier`
- `goldbach_autocorrelation_fourier`
- `goldbach_eta_zero`
- `goldbach_eta_inverse_fourier_nonnegative`

<!-- checkpoint-verification -->

## Verification

All 1243 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 5036-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 3926 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1245 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; the Section10/11 analytic and sieve estimates remain open internal obligations. The rational smooth multifrequency theorem with circle transference remains an explicit independent compound hypothesis. The classical primitive sum-of-two-squares criterion is an additional explicit independent arithmetic hypothesis for Section9 reductions; it contains no own-paper conclusion and is not declared as a Lean axiom.

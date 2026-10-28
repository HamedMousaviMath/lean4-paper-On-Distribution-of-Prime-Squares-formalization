# Checkpoint 1187: Complete source singular-integral positivity and comparison lemma

Every clause of l:positiveH9 is now proved for the genuine source functions. Fourier inversion applies to the actual continuous integrable logarithmic density, whose transform is exactly I_U(-gamma)J_(ell,W)(-gamma). The source n<N² support condition removes the strict progression restriction in the unsmoothed density, and the result is proved equal to the exact printed integral over2≤u≤U and2≤(n-u²)/ell≤W. Every endpoint and empty-domain case is included.

Combining that exact identity with the proved uniform smoothing comparison and actual-kernel positivity gives the complete lemma. One positive constant, depending only on the fixed seed, is chosen before N,ell,R,U,W,n. The theorem covers every real n<N², every positive ell,N,R and all U,W≥2 with U≤N; the source W≤N² restriction is unnecessary. Thus its range is at least the printed range.

The arbitrary real smooth compactly supported source seed is embedded into Schwartz space with nonzeroness proved. The normalized eta is proved equal to the actual autocorrelation integral divided by its actual squared-mass denominator, so the cutoff construction has not been substituted by an assumed surrogate.

A clause-by-clause source review closes l:positiveH9 as proved. All Section10 source statements are now complete except l:majorcompletion9. That major-completion lemma and the final l:circmethod assembly remain internal obligations. No new external theorem or own-paper endpoint was assumed. The manuscript is unchanged.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachPositiveSingularComplete.lean | 7 |

- `goldbach_archimedean_integral_domain`
- `goldbach_source_density_archimedean`
- `goldbach_source_unsmoothed_inverse`
- `goldbach_unsmoothed_archimedean_complete`
- `goldbach_smooth_compact_seed_nonzero`
- `goldbach_eta_of_smooth_compact_seed`
- `goldbach_positive_singular_integral_complete`

<!-- checkpoint-verification -->

## Verification

All 1254 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 5047-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 3975 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1256 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; the Section10/11 analytic and sieve estimates remain open internal obligations. The rational smooth multifrequency theorem with circle transference remains an explicit independent compound hypothesis. The classical primitive sum-of-two-squares criterion is an additional explicit independent arithmetic hypothesis for Section9 reductions; it contains no own-paper conclusion and is not declared as a Lean axiom.

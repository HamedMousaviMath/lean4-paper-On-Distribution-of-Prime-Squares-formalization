# Checkpoint 1186: Actual logarithmic density Fourier transform and endpoint continuity

The actual truncated logarithmic density is constructed, proved measurable, integrable and uniformly bounded. Its only possible discontinuities are its two endpoints, and continuity elsewhere is proved directly.

The exact quadratic average with the source cutoffs is proved globally integrable, and its Fourier transform is exactly I_U(-gamma)J_(ell,W)(-gamma). Pointwise continuity of the averaged density is also proved: the exceptional endpoint preimages are the explicitly excluded singleton square roots, which have zero measure. Dominated convergence uses the proved logarithmic bound, so no endpoint regularity is assumed.

These facts discharge every hypothesis of ordinary Fourier inversion for the actual source density. The next assembly identifies the inverse integral with the printed one-variable H_ell and closes the full positivity/comparison lemma.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachSourceDensity.lean | 8 |

- `goldbach_log_window_measurable`
- `goldbach_log_window_integrable`
- `goldbach_log_window_norm`
- `goldbach_log_window_continuousAt`
- `goldbach_log_window_oscillatory`
- `goldbach_source_density_integrable`
- `goldbach_source_density_fourier`
- `goldbach_source_density_continuous`

<!-- checkpoint-verification -->

## Verification

All 1253 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 5046-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 3968 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1255 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; the Section10/11 analytic and sieve estimates remain open internal obligations. The rational smooth multifrequency theorem with circle transference remains an explicit independent compound hypothesis. The classical primitive sum-of-two-squares criterion is an additional explicit independent arithmetic hypothesis for Section9 reductions; it contains no own-paper conclusion and is not declared as a Lean axiom.

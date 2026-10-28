# Checkpoint 1204: Uniform sharp-to-smooth singular integral comparison

The actual sharp frequency cutoff is compared with the actual autocorrelation cutoff. The proof bounds both against the unsmoothed integral using the proved two-sided oscillatory tail and the proved quadratic cutoff estimate. It gives a constant depending only on the seed, chosen before every arithmetic family, with error at most K N / sqrt(R). The empty linear integration domain is included; no singular-integral comparison is postulated.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachHardSmoothing.lean | 7 |

- `goldbach_hard_cutoff_measurable`
- `goldbach_hard_cutoff_norm`
- `goldbach_euclidean_product_phase_integrable`
- `goldbach_frequency_tail_norm`
- `goldbach_euclidean_product_phase_tail`
- `goldbach_hard_unsmoothed_comparison`
- `goldbach_hard_singular_smoothing_uniform`

<!-- checkpoint-verification -->

## Verification

All 1271 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 5064-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 4044 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1273 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; the Section10/11 analytic and sieve estimates remain open internal obligations. The rational smooth multifrequency theorem with circle transference remains an explicit independent compound hypothesis. The classical primitive sum-of-two-squares criterion is an additional explicit independent arithmetic hypothesis for Section9 reductions; it contains no own-paper conclusion and is not declared as a Lean axiom.

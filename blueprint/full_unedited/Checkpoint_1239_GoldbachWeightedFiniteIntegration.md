# Checkpoint 1239: Finite weighted integration and smoothing identities

Finite integration over variable upper intervals is checked with the original real endpoints and all integrability requirements: a finite sum of integrals over[a,b_i] equals the integral over[a,U] of the corresponding filtered finite sum. The ordinary outer prime products are proved to lie between0 and1. Two finite complex-to-real smoothing inequalities bound the weighted discrepancy by E times the reciprocal weight mass, with the extra outer factors absorbed using their proved[0,1] range.

The original archimedean integrals for every positive multiplier now have their literal real-integrand representation, uniform bounded-integrand integrability, nonnegativity, and the exact finite weighted sum/integral interchange. This includes the actual logarithmic window and the shift n-1; it does not substitute a power model for H_ell. These internally proved integration and smoothing tools will be applied to the quantitative weighted kernel bound. No new external input is used, and no own-paper endpoint has been assumed. The complete weighted comparison remains open until the two-variable estimate and final assembly are discharged.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachWeightedFiniteIntegration.lean | 4 |
| GoldbachWeightedArchimedean.lean | 4 |

- `goldbach_finite_variable_interval`
- `goldbach_weighted_outer_product_le_one`
- `goldbach_finite_smoothing_upper`
- `goldbach_finite_smoothing_outer_upper`
- `goldbach_weighted_arch_integrand_integrable`
- `goldbach_weighted_arch_real`
- `goldbach_weighted_arch_sum_identity`
- `goldbach_weighted_arch_integrand_nonneg`

<!-- checkpoint-verification -->

## Verification

All 1331 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 5124-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 4356 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1333 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; all Section10 statements and the full circle-method implication are complete in the agreed conditional scope; Section11 remains open. Earlier effective Wirsing and prime Mertens inputs retained. No new external input in finite integration, smoothing or archimedean identities. The full Section11 lower-sieve proposition p:sieveneedlower8 is a complete conditional implication, including its actual main term, uniform o(1), n-independent coefficients and mean-square error. The uniform main-term lower bound l:maintermsize8 and its joint application with the same large cutoff C are also complete conditionally. The weighted upper main-term sum, upper sieve, numerical comparison and final Goldbach conclusion remain open.

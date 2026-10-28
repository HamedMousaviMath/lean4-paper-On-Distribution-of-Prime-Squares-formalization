# Checkpoint 1237: Kernel calculus, exact W normalization and thin integration window

The rational logarithmic kernels used in both weighted summations have checked derivatives, signs and their precise quotient/log identity. The mean model A*x/sqrt(log x) has its checked derivative and upper density bound. These calculus facts apply on the explicit positive domains needed for Abel summation.

The constant integral is now the literal paper W(alpha), specialized to alpha=9/8. Lean evaluates the inner rational integral by a proved logarithmic primitive, proves its continuous dependence on r, its nonnegativity, and integrability of its r^(-1/2) weighted outer integral. An exact affine substitution proves I_(9/8)=8*sqrt(2)*W(9/8), including the endpoint r=0, without a numerical approximation. The original displayed W integrand is interval integrable and W(9/8)>=0. The square-root endpoint is handled using the integrable power-1/2, not omitted.

The discarded integration window is also controlled: for n>=4 and0<=T<=n/4, the measure of{y>=2:0<n-1-y^2<T} is at most2T/sqrt(n), with the exact square-root interval inclusion and width proved. No new deep input is used. Weighted Abel applications to the actual coefficient families, two-variable summation, smoothing and final normalization remain before closing l:wumatomakisum.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachWeightedKernels.lean | 7 |
| GoldbachWeightedIntegralConstant.lean | 10 |
| GoldbachWeightedThinWindow.lean | 3 |

- `goldbach_weighted_log_kernel_deriv`
- `goldbach_weighted_prime_kernel_deriv`
- `goldbach_weighted_counting_model_deriv`
- `goldbach_weighted_log_kernel_sign`
- `goldbach_weighted_prime_kernel_sign`
- `goldbach_weighted_counting_model_deriv_le`
- `goldbach_weighted_kernel_log_identity`
- `goldbach_weighted_inner_primitive_deriv`
- `goldbach_weighted_inner_integral`
- `goldbach_weighted_inner_closed`
- `goldbach_weighted_W_pointwise`
- `goldbach_weighted_W_identity`
- `goldbach_weighted_inner_continuous`
- `goldbach_weighted_inner_nonneg`
- `goldbach_weighted_outer_integrable`
- `goldbach_weighted_W_integrable`
- `goldbach_weighted_W_nonneg`
- `goldbach_weighted_thin_window_width`
- `goldbach_weighted_thin_window_subset`
- `goldbach_weighted_thin_window_measure`

<!-- checkpoint-verification -->

## Verification

All 1327 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 5120-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 4342 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1329 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; all Section10 statements and the full circle-method implication are complete in the agreed conditional scope; Section11 remains open. Earlier effective Wirsing and prime Mertens inputs retained. All calculus, W normalization and thin-window facts in this checkpoint are internal Lean proofs. The full Section11 lower-sieve proposition p:sieveneedlower8 is a complete conditional implication, including its actual main term, uniform o(1), n-independent coefficients and mean-square error. The uniform main-term lower bound l:maintermsize8 and its joint application with the same large cutoff C are also complete conditionally. The weighted upper main-term sum, upper sieve, numerical comparison and final Goldbach conclusion remain open.

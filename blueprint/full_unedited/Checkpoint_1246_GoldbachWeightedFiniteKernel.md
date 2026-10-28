# Checkpoint 1246: Weighted upper main term: actual finite kernel and scale limits

# Weighted upper main term: quantitative source kernel and scale limits

The source pair kernel now has one checked quantitative upper bound. Its inputs are the internally proved summatory and harmonic estimates; its output retains the exact W(9/8) term and all prime, floor, and boundary errors. The estimate concerns the actual pair sum, with no abstract replacement of the paper's main term.

The logarithmic scale limits are proved separately: the leading coefficient tends to the half-dimensional constant times W, and the small-denominator and prime endpoint coefficients tend to zero. These results use the pinned Mathlib asymptotic lemmas and explicit inequalities.

The final weighted upper main-term lemma still requires the uniform cutoff budgets, moving-logarithm comparison, and insertion into the normalized source singular integrals. No new external input is introduced.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachWeightedFiniteKernel.lean | 2 |
| GoldbachWeightedScaleLimits.lean | 5 |

- `goldbach_weighted_finite_kernel`
- `goldbach_weighted_prime_error_coarse`
- `goldbach_weighted_log_power_sqrt_limit`
- `goldbach_weighted_sqrt_log_inverse_limit`
- `goldbach_weighted_main_coefficient_limit`
- `goldbach_weighted_small_coefficient_limit`
- `goldbach_weighted_endpoint_coefficient_limit`

<!-- checkpoint-verification -->

## Verification

All 1345 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 5138-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 4399 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1347 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; all Section10 statements and the full circle-method implication are complete in the agreed conditional scope; Section11 remains open. Previously documented independent mean-value/Mertens inputs only. The full Section11 lower-sieve proposition p:sieveneedlower8 is a complete conditional implication, including its actual main term, uniform o(1), n-independent coefficients and mean-square error. The uniform main-term lower bound l:maintermsize8 and its joint application with the same large cutoff C are also complete conditionally. The weighted upper main-term sum, upper sieve, numerical comparison and final Goldbach conclusion remain open.

# Checkpoint 1251: Weighted upper main term: all uniform relative errors

# Weighted upper main term: uniform relative errors

Both errors are now bounded relative to the common positive reference C_R H_1(n) sqrt(log R/log N), using the actual retained range for n. With the truncation exponent A+14 and C >= A+24, the discarded-region error is bounded by a fixed multiple of (log N)^(-3), and the total smoothing error by a fixed multiple of (log N)^(-2), times that reference.

The lower singular integral has relative smoothing error at most 8K/log N. All scale restrictions, Mertens error tolerances, positive truncation heights, and the R-to-power-of-N comparisons are eventually valid with thresholds independent of n.

No paper-specific asymptotic error is assumed. These are proved inequalities and limits. The source weighted upper main-term lemma remains open only until the final checked assembly is staged.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachWeightedErrorBounds.lean | 7 |
| GoldbachWeightedSourceBudgets.lean | 1 |

- `goldbach_weighted_smoothing_relative`
- `goldbach_weighted_reference_lower_scalar`
- `goldbach_weighted_thin_ratio_scalar`
- `goldbach_weighted_thin_error_relative`
- `goldbach_weighted_smooth_error_relative`
- `goldbach_weighted_error_coefficient_limit`
- `goldbach_weighted_thin_cutoff`
- `goldbach_weighted_source_budgets`

<!-- checkpoint-verification -->

## Verification

All 1356 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 5149-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 4427 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1358 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; all Section10 statements and the full circle-method implication are complete in the agreed conditional scope; Section11 remains open. Previously documented independent mean-value/Mertens inputs only. The full Section11 lower-sieve proposition p:sieveneedlower8 is a complete conditional implication, including its actual main term, uniform o(1), n-independent coefficients and mean-square error. The uniform main-term lower bound l:maintermsize8 and its joint application with the same large cutoff C are also complete conditionally. The weighted upper main-term sum, upper sieve, numerical comparison and final Goldbach conclusion remain open.

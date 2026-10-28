# Checkpoint 1242: Weighted upper main term: source normalization and finite smoothing error

# Weighted upper main term: the source sum and smoothing error

The actual source sum over multipliers is now exactly normalized as a finite sum over the unique pairs (u,p), with the concrete B_R, h_R, Euler factors, and smoothed singular integrals. The geometric bounds place every pair in the required sieve range. Applying the existing uniform smoothing theorem gives an explicit total error bounded by 6 B_R K N/sqrt(R) times the actual reciprocal weight mass.

A separate finite fiber argument bounds the weighted pair sum by the explicit prime-by-denominator rectangle. It preserves the p=z endpoint and the inclusive upper floor. The proof includes the coverage of the actual source pairs and all nonnegativity needed to enlarge the summation domain.

The weighted upper main-term source claim remains open pending the sharp double-sum bound and uniform error assembly. No new deep input is used, and no manuscript edits are applied.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachWeightedSmoothing.lean | 3 |
| GoldbachWeightedRectangles.lean | 3 |

- `goldbach_weighted_pair_levels`
- `goldbach_weighted_main_term_sum_normalization`
- `goldbach_weighted_main_term_smoothing`
- `goldbach_finite_fiber_upper`
- `goldbach_weighted_pair_rectangle`
- `goldbach_weighted_kernel_rectangle`

<!-- checkpoint-verification -->

## Verification

All 1337 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 5130-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 4378 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1339 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; all Section10 statements and the full circle-method implication are complete in the agreed conditional scope; Section11 remains open. Previously documented independent mean-value/Mertens inputs only. The full Section11 lower-sieve proposition p:sieveneedlower8 is a complete conditional implication, including its actual main term, uniform o(1), n-independent coefficients and mean-square error. The uniform main-term lower bound l:maintermsize8 and its joint application with the same large cutoff C are also complete conditionally. The weighted upper main-term sum, upper sieve, numerical comparison and final Goldbach conclusion remain open.

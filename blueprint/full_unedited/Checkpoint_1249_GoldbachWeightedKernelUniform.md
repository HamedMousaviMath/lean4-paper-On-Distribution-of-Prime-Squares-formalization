# Checkpoint 1249: Weighted upper main term: sharp uniform moving kernel complete

# Weighted upper main term: sharp uniform kernel estimate

The weighted kernel estimate is complete in epsilon form. For every fixed positive cutoff exponent C and every eta>0, the actual finite source pair kernel is eventually bounded by (kappa W(9/8)+eta)(C_R/B_R)/(sqrt(log R) log N sqrt(log N)), uniformly in n.

The same sharp bound holds for every m between N^2(log N)^(-A) and N^2. The proof controls the moving logarithmic denominator, respects its support filter, and chooses a positive tolerance using a checked continuity argument. All effective mean hypotheses are discharged by the proved cutoff budgets; no paper-specific estimate remains among the independent inputs.

The full source main-term claim still requires insertion into the singular integrals, total smoothing and discarded-region errors, and comparison with the lower main term. The existing independent mean-value and Mertens assumptions are unchanged.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachWeightedKernelUniform.lean | 2 |
| GoldbachWeightedMovingKernel.lean | 3 |

- `goldbach_weighted_choose_mean_parameter`
- `goldbach_weighted_fixed_kernel_uniform`
- `goldbach_choose_positive_tolerance`
- `goldbach_weighted_moving_kernel_loss`
- `goldbach_weighted_moving_kernel_uniform`

<!-- checkpoint-verification -->

## Verification

All 1352 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 5145-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 4414 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1354 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; all Section10 statements and the full circle-method implication are complete in the agreed conditional scope; Section11 remains open. Previously documented independent mean-value/Mertens inputs only. The full Section11 lower-sieve proposition p:sieveneedlower8 is a complete conditional implication, including its actual main term, uniform o(1), n-independent coefficients and mean-square error. The uniform main-term lower bound l:maintermsize8 and its joint application with the same large cutoff C are also complete conditionally. The weighted upper main-term sum, upper sieve, numerical comparison and final Goldbach conclusion remain open.

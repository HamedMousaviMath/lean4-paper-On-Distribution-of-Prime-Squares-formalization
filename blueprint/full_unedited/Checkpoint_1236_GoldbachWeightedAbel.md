# Checkpoint 1236: Quantitative Abel estimates and exact multiplier parametrization

Two quantitative real Abel estimates and their full model-error identity are kernel checked. One consumes an upper bound for a nonnegative summatory function against a decreasing positive weight, including the exact lower-boundary term. The other compares an increasing positive weighted sum to a differentiable model with bounded cumulative error, with the explicit error2B*f(b). All endpoints, finite floor cutoffs, integrability and integration by parts are proved.

The actual closed multiplier set L is proved to be the image of its finite(u,p2) pairs, and the map(u,p2)->2*u*p2 is injective on this set. Its proof uses the disjoint1 mod4 support of u and3 mod4 prime p2. Hence finite sums over the original L equal sums over the parametrizing pairs, with no multiplicity assumed away. The actual reciprocal weighted pair mass has a uniform logarithmic power7 bound derived from the preceding harmonic theorem and the elementary harmonic sum. No new deep input is used. The full weighted source inequality remains open; the new general Abel facts are proved tools for its internal analytic deduction.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachWeightedAbel.lean | 3 |
| GoldbachWeightedPairs.lean | 6 |

- `goldbach_abel_model_identity`
- `goldbach_abel_decreasing_upper`
- `goldbach_abel_increasing_error`
- `goldbach_weighted_pair_multiplier`
- `mem_goldbach_weighted_pairs`
- `goldbach_weighted_pair_injective`
- `goldbach_weighted_pairs_image`
- `goldbach_weighted_pairs_sum`
- `goldbach_weighted_pairs_harmonic`

<!-- checkpoint-verification -->

## Verification

All 1324 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 5117-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 4322 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1326 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; all Section10 statements and the full circle-method implication are complete in the agreed conditional scope; Section11 remains open. Existing effective mean-value and Mertens inputs retained. This checkpoint introduces no new external input. The full Section11 lower-sieve proposition p:sieveneedlower8 is a complete conditional implication, including its actual main term, uniform o(1), n-independent coefficients and mean-square error. The uniform main-term lower bound l:maintermsize8 and its joint application with the same large cutoff C are also complete conditionally. The weighted upper main-term sum, upper sieve, numerical comparison and final Goldbach conclusion remain open.

# Checkpoint 1245: Weighted upper main term: sharp finite double sum and cutoff split

# Weighted upper main term: sharp finite rectangle estimate

The two checked Abel estimates and the checked logarithmic changes of variables now give the finite large-denominator estimate. Its leading coefficient is the exact paper integral W(9/8). Prime endpoints, logarithmic Mertens errors, and the summatory boundary are explicit additional terms.

The actual source pair kernel is split at a real cutoff a. The small-denominator part is bounded by its weighted harmonic sum and a prime reciprocal sum. The large part is placed in the active rectangle, with the actual floors and logarithmic denominators preserved. All enlargements use proved nonnegative weights.

No error term is silently discarded. The source comparison remains open until these explicit terms are shown to be uniformly negligible and inserted into the source main-term normalization. No new external theorem is assumed.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachWeightedLargeRectangle.lean | 1 |
| GoldbachWeightedKernelSplit.lean | 3 |

- `goldbach_weighted_large_rectangle`
- `goldbach_weighted_pair_log_floor`
- `goldbach_weighted_kernel_small`
- `goldbach_weighted_kernel_large`

<!-- checkpoint-verification -->

## Verification

All 1343 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 5136-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 4392 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1345 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; all Section10 statements and the full circle-method implication are complete in the agreed conditional scope; Section11 remains open. Previously documented independent mean-value/Mertens inputs only. The full Section11 lower-sieve proposition p:sieveneedlower8 is a complete conditional implication, including its actual main term, uniform o(1), n-independent coefficients and mean-square error. The uniform main-term lower bound l:maintermsize8 and its joint application with the same large cutoff C are also complete conditionally. The weighted upper main-term sum, upper sieve, numerical comparison and final Goldbach conclusion remain open.

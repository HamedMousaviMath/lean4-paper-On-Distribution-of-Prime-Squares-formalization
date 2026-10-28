# Checkpoint 1240: Weighted upper main term: integration and logarithmic geometry

# Weighted upper main term: integration and logarithmic geometry

The real Archimedean integrals now reduce to the actual finite weighted logarithmic kernel sum. The comparison uses H_1(n) directly. The discarded region is bounded by 2T/sqrt(n) times the reciprocal weight mass, divided by (log 2)^3. All support restrictions and integrability arguments are proved.

The two changes of variables p=exp(Dv), u=exp(Dr)/2 are checked. They identify the resulting iterated integral with the existing exact integral for 8 sqrt(2) W(9/8). This includes extension to the integrable r=0 endpoint. No numerical or asymptotic estimate is used in that identity.

This checkpoint does not assert the weighted upper main-term lemma. The double finite sum, endpoint errors, small-u contribution, and final uniform comparison remain to be assembled. The independent mean-value and Mertens inputs retain their previously documented scope; no new external input is introduced.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachWeightedKernelIntegration.lean | 5 |
| GoldbachWeightedMellin.lean | 3 |

- `goldbach_weighted_arch_pointwise`
- `goldbach_weighted_arch_sum_pointwise`
- `goldbach_weighted_arch_retained_pointwise`
- `goldbach_weighted_arch_coarse`
- `goldbach_weighted_arch_kernel_integrated`
- `goldbach_weighted_inner_mellin`
- `goldbach_weighted_outer_mellin`
- `goldbach_weighted_outer_mellin_le_W`

<!-- checkpoint-verification -->

## Verification

All 1333 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 5126-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 4364 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1335 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; all Section10 statements and the full circle-method implication are complete in the agreed conditional scope; Section11 remains open. Previously documented independent mean-value/Mertens inputs only. The full Section11 lower-sieve proposition p:sieveneedlower8 is a complete conditional implication, including its actual main term, uniform o(1), n-independent coefficients and mean-square error. The uniform main-term lower bound l:maintermsize8 and its joint application with the same large cutoff C are also complete conditionally. The weighted upper main-term sum, upper sieve, numerical comparison and final Goldbach conclusion remain open.

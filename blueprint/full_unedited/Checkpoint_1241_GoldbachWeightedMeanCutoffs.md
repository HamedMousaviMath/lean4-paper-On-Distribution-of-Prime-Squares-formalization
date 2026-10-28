# Checkpoint 1241: Weighted upper main term: small denominators and comparison losses

# Weighted upper main term: small denominators and comparison losses

The strongly multiplicative weight now has a uniform coarse mean estimate for x at least R^D, with constants chosen before R and n. A finite Abel argument gives a harmonic tail estimate from a linear summatory bound. Combining this with the already checked finite Euler-product majorant controls all small denominators, including those outside the effective half-dimensional mean range.

Prime reciprocal sums are bounded from the independent logarithmic Mertens input. The factor introduced when replacing log u by log(2u), the retained-region logarithmic loss, and 3 sqrt(alpha) c_alpha = 48 exp(-gamma/2)/sqrt(pi) are checked exactly.

The weighted upper main-term source claim stays open until the finite double sum, integration, and uniform relative errors have all been assembled. No new external input is introduced and the selected manuscript is unchanged.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachWeightedMeanCutoffs.lean | 4 |
| GoldbachWeightedLogComparisons.lean | 4 |

- `goldbach_weighted_mean_coarse`
- `goldbach_weighted_prime_reciprocal`
- `goldbach_harmonic_tail_linear`
- `goldbach_weighted_harmonic_refined`
- `goldbach_weighted_log_offset`
- `goldbach_weighted_log_loss`
- `goldbach_weighted_upper_constant_positive`
- `goldbach_weighted_upper_constant_normalization`

<!-- checkpoint-verification -->

## Verification

All 1335 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 5128-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 4372 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1337 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; all Section10 statements and the full circle-method implication are complete in the agreed conditional scope; Section11 remains open. Previously documented independent mean-value/Mertens inputs only. The full Section11 lower-sieve proposition p:sieveneedlower8 is a complete conditional implication, including its actual main term, uniform o(1), n-independent coefficients and mean-square error. The uniform main-term lower bound l:maintermsize8 and its joint application with the same large cutoff C are also complete conditionally. The weighted upper main-term sum, upper sieve, numerical comparison and final Goldbach conclusion remain open.

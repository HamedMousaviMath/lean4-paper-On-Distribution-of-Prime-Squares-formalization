# Checkpoint 1244: Weighted upper main term: logarithmic region and sharp integral

# Weighted upper main term: the double-integral region

The logarithmic region for the two summation orders is checked: u <= exp(D)/(2p^2) is equivalent to p <= exp((D-log(2u))/2). Its bounds imply all derivative signs and nonvanishing denominators needed by the two Abel estimates.

The resulting integral is bounded sharply by sqrt(1+log(2)/log(a)) sqrt(D) 8 sqrt(2) W(9/8). The factor records the replacement of log(u) by log(2u) and tends to one at the intended cutoff. A separate explicit integral bound controls the prime endpoint and Mertens errors.

These are internal proved analytic steps. The independent mean-value and Mertens boundaries are unchanged. The source upper main-term comparison is still open pending finite assembly and uniform relative error estimates.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachWeightedDoubleGeometry.lean | 4 |
| GoldbachWeightedDoubleIntegral.lean | 3 |

- `goldbach_weighted_u_bound_log`
- `goldbach_weighted_double_p_geometry`
- `goldbach_weighted_double_u_geometry`
- `goldbach_weighted_double_domain`
- `goldbach_weighted_log_harmonic_integral_le`
- `goldbach_weighted_double_integrands_continuous`
- `goldbach_weighted_double_integral_le_W`

<!-- checkpoint-verification -->

## Verification

All 1341 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 5134-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 4388 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1343 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; all Section10 statements and the full circle-method implication are complete in the agreed conditional scope; Section11 remains open. Previously documented independent mean-value/Mertens inputs only. The full Section11 lower-sieve proposition p:sieveneedlower8 is a complete conditional implication, including its actual main term, uniform o(1), n-independent coefficients and mean-square error. The uniform main-term lower bound l:maintermsize8 and its joint application with the same large cutoff C are also complete conditionally. The weighted upper main-term sum, upper sieve, numerical comparison and final Goldbach conclusion remain open.

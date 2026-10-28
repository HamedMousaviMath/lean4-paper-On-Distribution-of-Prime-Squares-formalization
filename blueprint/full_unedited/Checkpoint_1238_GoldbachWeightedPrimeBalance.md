# Checkpoint 1238: Actual prime and varying-weight Abel applications

The actual primes3 mod4 logarithmic summatory function is now controlled from the independent ordinary and1 mod4 Mertens input. Lean proves the exact prime partition including the prime2 correction, and an absolute discrepancy bound2K+1. Its concrete increasing-kernel Abel application gives the prime weighted integral with the explicit endpoint error2*(2K+1)*g(b), with all derivatives, signs and integrability proved.

The decreasing-kernel application to the actual varying multiplicative weight is also complete. It gives an integral against A/(t*sqrt(log t)) plus the exact lower-boundary term A/(sqrt(log a)*L(a)^2). The theorem goldbach_weighted_mean_abel_effective instantiates this with the normalized effective mean-value theorem: Kmean and delta are chosen once before R,n and every interval. Conditions imposed at the lower interval endpoint propagate to every t in the interval by proved monotonicity of logs and powers. No interval-specific mean-value estimate is assumed. These two quantitative one-variable applications are the inputs to the remaining two-variable summation. The full source weighted comparison stays open; no new external input is introduced.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachWeightedPrimeBalance.lean | 4 |
| GoldbachWeightedMeanAbel.lean | 2 |

- `goldbach_three_prime_log_partition`
- `goldbach_three_log_summatory`
- `goldbach_three_log_mertens`
- `goldbach_weighted_prime_abel`
- `goldbach_weighted_mean_abel`
- `goldbach_weighted_mean_abel_effective`

<!-- checkpoint-verification -->

## Verification

All 1329 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 5122-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 4348 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1331 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; all Section10 statements and the full circle-method implication are complete in the agreed conditional scope; Section11 remains open. Existing effective Wirsing and ordinary/progression Mertens inputs retained. No new external input in these concrete Abel applications. The full Section11 lower-sieve proposition p:sieveneedlower8 is a complete conditional implication, including its actual main term, uniform o(1), n-independent coefficients and mean-square error. The uniform main-term lower bound l:maintermsize8 and its joint application with the same large cutoff C are also complete conditionally. The weighted upper main-term sum, upper sieve, numerical comparison and final Goldbach conclusion remain open.

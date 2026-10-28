# Checkpoint 1233: Uniform prime balance and effective mean-value instantiation

The varying multiplicative weights now have a checked quantitative prime logarithmic balance. For every y>=R>=3, uniformly in n, the absolute value of sum_{p<=y}(h_R(p)-1/2)log(p)/p is at most6 log R+10K, from the independent ordinary/progression logarithmic Mertens input. The strong prime-power rule and the equality at prime arguments are checked.

The general nonnegative strongly multiplicative upper corollary of Tenenbaum's corrected effective Wirsing theorem is an explicit independent proposition-valued input. The exact instantiation to h_R is proved in goldbach_weighted_mean_from_tenenbaum, with Kmean and delta fixed before R,n,x,epsilon. All applicability requirements, including R<=x^epsilon and6 log R+10K<=epsilon^2 log x, are explicit and verified in the consuming proof. The input contains no Goldbach sequence, h_R, multiplier set, singular integral or paper main term. Its general corollary derivation and remaining external scope are recorded in docs/EXTERNAL_WEIGHTED_MEAN_INPUTS.md. No new Lean axiom or unchecked proof is introduced. Full weighted summation, integration and the final upper comparison remain internal obligations; l:wumatomakisum remains open.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachWeightedMeanInputs.lean | 9 |

- `goldbach_half_mean_constant_positive`
- `goldbach_weighted_prime_power`
- `goldbach_weighted_at_prime`
- `goldbach_weighted_prime_above`
- `goldbach_baseline_prime_range`
- `goldbach_weighted_prime_difference`
- `goldbach_baseline_prime_log_balance`
- `goldbach_weighted_prime_log_balance`
- `goldbach_weighted_mean_from_tenenbaum`

<!-- checkpoint-verification -->

## Verification

All 1319 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 5112-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 4291 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1321 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; all Section10 statements and the full circle-method implication are complete in the agreed conditional scope; Section11 remains open. The effective Wirsing theorem and the independent prime logarithmic Mertens facts remain explicit inputs. Their exact application to the actual R-dependent weights is proved. See EXTERNAL_WEIGHTED_MEAN_INPUTS.md. The full Section11 lower-sieve proposition p:sieveneedlower8 is a complete conditional implication, including its actual main term, uniform o(1), n-independent coefficients and mean-square error. The uniform main-term lower bound l:maintermsize8 and its joint application with the same large cutoff C are also complete conditionally. The weighted upper main-term sum, upper sieve, numerical comparison and final Goldbach conclusion remain open.

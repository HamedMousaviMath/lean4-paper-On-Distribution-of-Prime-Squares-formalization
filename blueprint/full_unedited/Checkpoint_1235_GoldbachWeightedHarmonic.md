# Checkpoint 1235: Uniform harmonic control and normalized upper mean values

The actual varying weight has a checked uniform harmonic bound: sum_{u<=U}h_R(u)/u<=3*((1+K/log2)*(log(U+1)/log2)^2)^3 for U>=2, independently of n and R. The proof embeds the finite sum in the divisors of floor(U)!, expands the multiplicative divisor sum, bounds geometric prime-power sums, separates5, and uses the existing preliminary interval-product Mertens input. No Shiu conclusion is assumed.

The finite Euler product in the effective mean value is exactly(C_R/B_R) times the ordinary inverse prime product on R<p<=x, p=1 mod4. Consuming standard ordinary/progression Mertens ratios gives sum_{u<=x}h_R(u)<=(kappa+Kmean*epsilon^delta)*(1+Km/log R)*(C_R/B_R)*x/(sqrt(log R)*sqrt(log x)), with kappa=exp(-gamma/2)/sqrt(pi). Kmean and delta are fixed before R,n,x andepsilon. Every condition of the effective mean-value input is retained and internally checked. The additional ratio input contains only fixed-progression prime products. No own-paper weighted summation or integration endpoint is assumed; l:wumatomakisum remains open.

A staging preflight issue was reconciled before compilation or any save attempt: identical draft copies were verified, and their temporary import/audit entries were removed and restaged after preparing the missing scope. The driver now reads the reviewed scope before staging. The reconciliation is recorded; no earlier proof source was changed.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachWeightedHarmonic.lean | 5 |
| GoldbachWeightedMeanValue.lean | 3 |

- `goldbach_weighted_prime_harmonic_local`
- `goldbach_weighted_harmonic_divisors`
- `goldbach_weighted_harmonic_local_majorant`
- `goldbach_weighted_harmonic_product`
- `goldbach_weighted_harmonic_uniform`
- `goldbach_weighted_correction_product`
- `goldbach_weighted_euler_split`
- `goldbach_weighted_mean_normalized`

<!-- checkpoint-verification -->

## Verification

All 1322 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 5115-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 4313 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1324 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; all Section10 statements and the full circle-method implication are complete in the agreed conditional scope; Section11 remains open. Effective mean-value and ordinary/progression Mertens facts remain independent inputs; normalized applications and the harmonic estimate are Lean proofs. The full Section11 lower-sieve proposition p:sieveneedlower8 is a complete conditional implication, including its actual main term, uniform o(1), n-independent coefficients and mean-square error. The uniform main-term lower bound l:maintermsize8 and its joint application with the same large cutoff C are also complete conditionally. The weighted upper main-term sum, upper sieve, numerical comparison and final Goldbach conclusion remain open.

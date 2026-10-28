# Checkpoint 1231: Weighted upper local cancellations and uniform prime weights

The first weighted upper-main-term component is checked. The local joint factor U_p, the exact prime weights h_R(p), their multiplicative extension, and B_R(n), C_R(n) are concrete definitions. Lean proves positivity of the joint denominator for every prime p>3, treating p=5 by the finite consecutive-residue calculation. It proves 0<=h_R(p)<=6 uniformly, both exact small-prime cancellation identities, the lower and upper local-density cancellations, multiplicativity and nonnegativity of h_R, and 0<B_R(n)<=C_R(n).

No new external input is used. These are internal arithmetic steps of l:wumatomakisum, not a proof of the full weighted comparison. Remaining: exact finite-product assembly with the original G and Theta; uniform multiplicative mean values and weighted summation; integration, smoothing and the final normalized constant. The source-level claim stays open. The large-m cutoff in Step6 must remain explicit; its displayed logarithmic-power integral cannot literally be extended to every m>0 without an indicator. The selected manuscript remains unchanged.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachWeightedLocalFactors.lean | 13 |

- `goldbach_joint_denominator_positive`
- `goldbach_joint_local_positive`
- `goldbach_weighted_prime_nonneg`
- `goldbach_weighted_prime_le_six`
- `goldbach_weighted_small_prime_cancel`
- `goldbach_weighted_lower_local_cancel`
- `goldbach_weighted_upper_local_cancel`
- `goldbach_weighted_multiplicative_one`
- `goldbach_weighted_multiplicative_nonneg`
- `goldbach_weighted_multiplicative_mul`
- `goldbach_weighted_B_positive`
- `goldbach_weighted_B_le_C`
- `goldbach_weighted_C_positive`

<!-- checkpoint-verification -->

## Verification

All 1316 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 5109-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 4272 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1318 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; all Section10 statements and the full circle-method implication are complete in the agreed conditional scope; Section11 remains open. No new external input in the local weighted upper arithmetic. The full Section11 lower-sieve proposition p:sieveneedlower8 is a complete conditional implication, including its actual main term, uniform o(1), n-independent coefficients and mean-square error. The uniform main-term lower bound l:maintermsize8 and its joint application with the same large cutoff C are also complete conditionally. The weighted upper main-term sum, upper sieve, numerical comparison and final Goldbach conclusion remain open.

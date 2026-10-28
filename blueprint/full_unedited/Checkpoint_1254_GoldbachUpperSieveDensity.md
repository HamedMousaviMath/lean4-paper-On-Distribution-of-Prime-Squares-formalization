# Checkpoint 1254: Upper-sieve densities and uniform level geometry

The upper sieve now has the exact density and scale prerequisites. Its preliminary dimension2 includes the exceptional prime5 with barrier1/2; its outer dimension1 follows from an explicitly independent all-prime interval Mertens input. The new interface contains only finite products over arbitrary prime subsets and no Goldbach sequence, local roots, main terms or paper conclusions. It is the all-prime counterpart of the already documented interval Mertens boundary.

For every fixed B>=0 and C, the actual levels z_ell=(N^2/ell)^(1/4) and D_ell=sqrt(N^2/ell)/(12(log N)^B) satisfy R+1<=z_ell<=D_ell/D0<=N^2 eventually, uniformly for1<=ell<=N^(10/9). The exact logarithmic identity proves log(D_ell/D0)/log z_ell tends to2 along every admissible varying multiplier path. The eventual uniformization and source application are next. No own-paper endpoint has been assumed.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachUpperSieveDensity.lean | 5 |
| GoldbachUpperSieveParameters.lean | 6 |

- `goldbach_upper_sieve_prime_ge_five`
- `goldbach_upper_prime_split`
- `goldbach_upper_density_multiplicative`
- `goldbach_upper_preliminary_dimension`
- `goldbach_upper_outer_dimension`
- `goldbach_upper_log_loss_ratio`
- `goldbach_upper_sieve_log_geometry`
- `goldbach_upper_outer_log`
- `goldbach_upper_sieve_levels_uniform`
- `goldbach_upper_parameter_along`
- `goldbach_upper_product_level`

<!-- checkpoint-verification -->

## Verification

All 1361 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 5154-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 4444 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1363 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; all Section10 statements and the full circle-method implication are complete in the agreed conditional scope; Section11 is complete through the weighted main-term comparison; the upper sieve and final Goldbach deductions remain open. Independent general effective mean-value and classical Mertens hypotheses remain explicit and unproved; all own weighted upper main-term deductions are complete. Earlier independent theorem scopes are unchanged. The full Section11 lower-sieve proposition p:sieveneedlower8 is a complete conditional implication, including its actual main term, uniform o(1), n-independent coefficients and mean-square error. The uniform main-term lower bound l:maintermsize8 and its joint application with the same large cutoff C are also complete conditionally. The full weighted upper main-term comparison l:wumatomakisum is a complete checked implication from the documented independent effective mean-value and Mertens inputs, with the exact printed constant and uniform retained-range quantifiers. The upper sieve, numerical comparison and final Goldbach conclusion remain open.

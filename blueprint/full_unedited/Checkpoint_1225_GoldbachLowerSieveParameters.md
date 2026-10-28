# Checkpoint 1225: Actual lower-sieve levels and refined density conditions

The actual lower-sieve levels D=N/(24(log N)^B), D1=D/exp((log log N)^3), and z=N^(8/9) now have a proved normalized logarithmic limit log(D1)/log(N) -> 1 and sieve-parameter limit log(D1)/log(z) -> 9/8. The entire admissible range R+1<=z<=D1<=N^2 is proved eventually for every fixed B and C, and D0*D1=D is exact. The finite prime set and its disjoint preliminary/outer split are explicit. The actual unit-square local densities yield a supported multiplicative density with all prime factors in [0,1). Both refined dimension conditions are proved from independent classical interval Mertens products. The preliminary majorant is 2/(p-3), p>=7, of dimension2; the outer product is the ordinary p=3 mod4 comparison of dimension1/2. This input contains no n, Goldbach sequence, presieve conclusion, or own-paper endpoint. The real lower application and circle-error assembly remain to be joined. The manuscript is unchanged while the user edits the supplied replacements.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachLowerSieveParameters.lean | 6 |
| GoldbachLowerSieveDensity.lean | 7 |

- `goldbach_lower_outer_level_pos`
- `goldbach_lower_outer_log`
- `goldbach_lower_outer_log_ratio`
- `goldbach_lower_sieve_parameter_tendsto`
- `goldbach_lower_sieve_levels_eventually`
- `goldbach_lower_product_level`
- `mem_goldbach_lower_sieve_primes`
- `goldbach_lower_prime_ge_seven`
- `goldbach_lower_prime_split`
- `goldbach_lower_prime_density_range`
- `goldbach_lower_density_multiplicative`
- `goldbach_lower_preliminary_dimension`
- `goldbach_lower_outer_dimension`

<!-- checkpoint-verification -->

## Verification

All 1306 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 5099-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 4217 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1308 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; all Section10 statements and the full circle-method implication are complete in the agreed conditional scope; Section11 remains open. Existing independent classical inputs remain explicit. Classical interval Mertens products for the universal majorant and the progression3 mod4 are additional independent arithmetic inputs; no own-paper endpoint is assumed.

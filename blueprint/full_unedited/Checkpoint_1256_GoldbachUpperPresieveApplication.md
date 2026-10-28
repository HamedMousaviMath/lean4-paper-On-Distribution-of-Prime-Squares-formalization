# Checkpoint 1256: Actual upper sieve and summed error estimates

The actual source upper sieve is assembled at each multiplier, including the vanishing arithmetic-factor case, and summed over the corrected closed multiplier set. All coefficients have absolute value at most1 and are chosen before n. The original double sum of remainders is embedded injectively into the circle-method coefficient family with L0=N^(6/5) and delta=3/4. The shift n-1, the factor12, strict divisor levels and all coprime residue requirements are checked. The complete shifted mean square is bounded by2M N^4(log N)^(-A).

The fixed-sieve comparison uses exactly the previously proved K N^(1/4) correction. Adding it to the summed remainder yields a mean square at most(4M+2K^2)N^4(log N)^(-A), for large N. The proof conservatively bounds its squared total by O(N^3), which is sufficient for every logarithmic saving.

A new record collects only the previously explicit independent classical inputs and normalizations; it contains no manuscript endpoint. The exact numerical gap follows from these general normalized values. The final upper coefficient assembly and common-cutoff lower/upper closure are next. No new deep input is added.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachUpperPresieveApplication.lean | 3 |
| GoldbachUpperFixedSieve.lean | 1 |
| GoldbachUpperSieveRemainder.lean | 2 |
| GoldbachUpperSieveErrors.lean | 2 |
| GoldbachSection11Inputs.lean | 1 |

- `goldbach_upper_remainder_zero_extension`
- `goldbach_upper_sifted_sequence`
- `goldbach_upper_presieve_application`
- `goldbach_upper_fixed_sieve_analytic`
- `goldbach_sieve_circle_bound_exists_above`
- `goldbach_upper_remainder_from_circle`
- `goldbach_upper_error_square_sum`
- `goldbach_upper_arithmetic_error_eventually`
- `goldbach_section11_sieve_gap_positive`

<!-- checkpoint-verification -->

## Verification

All 1368 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 5161-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 4459 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1370 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; all Section10 statements and the full circle-method implication are complete in the agreed conditional scope; Section11 is complete through the weighted main-term comparison; the upper sieve and final Goldbach deductions remain open. Independent general effective mean-value and classical Mertens hypotheses remain explicit and unproved; all own weighted upper main-term deductions are complete. Earlier independent theorem scopes are unchanged. The full Section11 lower-sieve proposition p:sieveneedlower8 is a complete conditional implication, including its actual main term, uniform o(1), n-independent coefficients and mean-square error. The uniform main-term lower bound l:maintermsize8 and its joint application with the same large cutoff C are also complete conditionally. The full weighted upper main-term comparison l:wumatomakisum is a complete checked implication from the documented independent effective mean-value and Mertens inputs, with the exact printed constant and uniform retained-range quantifiers. The upper sieve, numerical comparison and final Goldbach conclusion remain open.

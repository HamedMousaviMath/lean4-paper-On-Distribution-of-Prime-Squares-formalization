# Checkpoint 1253: Exact normalized sieve comparison

The source numerical comparison l:numericalcomparison is complete conditional only on the classical normalization of the independent sieve functions. Lean proves 8 sqrt(2) W(9/8)<=9/32 by bounding the actual inner integrand, integrating the two real powers exactly, and using the previously checked W change of variables. It then proves c_(9/8) exp(gamma) W(9/8)<=3 exp(gamma/2)/(8 sqrt(pi)), whereas the lower coefficient is (2 sqrt(2)/3) log(2) exp(gamma/2)/sqrt(pi). The elementary exact inequality log(2)>=1/2 already makes the difference strictly positive. This proves more than a floating-point calculation: every integral comparison and algebraic inequality is kernel checked. The printed weaker W bound remains valid. No new manuscript correction is needed here. The existing decimal claim >0.17 is not used or credited by this checkpoint; the required strict positivity is proved.

The generic functions in the independent sieve interfaces retain explicit normalization identities at9/8 and2. These identities belong to the classical general sieve boundary (Iwaniec1980,(1.8)-(1.10)); they are not a paper conclusion or an added Lean axiom. A source retrieval attempt identified the publisher DOI10.4064/aa-36-2-171-202 but its PDF hosts denied access in this run; the formal theorem transparently retains both normalization identities as hypotheses.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachSieveNumericalComparison.lean | 4 |

- `goldbach_weighted_inner_linear_upper`
- `goldbach_weighted_W_rational_upper`
- `goldbach_sieve_numerical_comparison`
- `goldbach_normalized_sieve_comparison`

<!-- checkpoint-verification -->

## Verification

All 1359 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 5152-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 4433 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1361 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; all Section10 statements and the full circle-method implication are complete in the agreed conditional scope; Section11 is complete through the weighted main-term comparison; the upper sieve and final Goldbach deductions remain open. Independent general effective mean-value and classical Mertens hypotheses remain explicit and unproved; all own weighted upper main-term deductions are complete. Earlier independent theorem scopes are unchanged. The full Section11 lower-sieve proposition p:sieveneedlower8 is a complete conditional implication, including its actual main term, uniform o(1), n-independent coefficients and mean-square error. The uniform main-term lower bound l:maintermsize8 and its joint application with the same large cutoff C are also complete conditionally. The full weighted upper main-term comparison l:wumatomakisum is a complete checked implication from the documented independent effective mean-value and Mertens inputs, with the exact printed constant and uniform retained-range quantifiers. The upper sieve, numerical comparison and final Goldbach conclusion remain open.

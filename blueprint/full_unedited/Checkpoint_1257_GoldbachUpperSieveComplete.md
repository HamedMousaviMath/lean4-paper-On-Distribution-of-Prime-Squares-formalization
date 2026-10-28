# Checkpoint 1257: Full upper-sieve proposition complete

The full source proposition p:sieveneedupper8 is complete. For every A0>0 and desired logarithmic mean-square saving A>0, a single B and C>=A0+24 is chosen before the tolerance. For every eta>0 and all large N, coefficients independent of n give the actual upper count at most(c_(9/8) F_1(2) W(9/8)+eta) X_n Theta_n(z)+E2(n), uniformly for retained admissible n. The actual E2 is the checked shifted double remainder plus the fixed-sieve K N^(1/4) correction; its full mean square is O(N^4(log N)^(-A)). No source main term, prime-counting weight or sieve endpoint is a hypothesis.

The checked theorem uses the explicit independent general input record described in docs/SECTION_11_UPPER_SIEVE_INPUTS.md. It includes the general sieve-function normalization and continuity, general one-stage sieve theorems, ordinary Mertens estimates and the effective mean-value theorem; their proofs remain external in the agreed scope.

The lower analytic theorem is now exported for every fixed B,C, and its exact mean-square remainder can be transported from the same circle bound as the upper remainder. This removes a possible mismatch between separately existential cutoff choices. The final common-cutoff Section11 theorem is next. The literal weaker presieving manuscript statement still requires its saved hypothesis replacements; no unsupported source claim is silently promoted.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachUpperSieveComplete.lean | 2 |
| GoldbachLowerFixedSieve.lean | 1 |
| GoldbachLowerCommonCircle.lean | 1 |

- `goldbach_upper_sieve_fixed_circle`
- `goldbach_upper_sieve_complete`
- `goldbach_lower_sieve_fixed_analytic`
- `goldbach_lower_remainder_from_circle`

<!-- checkpoint-verification -->

## Verification

All 1371 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 5164-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 4463 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1373 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; all Section10 statements and the full circle-method implication are complete in the agreed conditional scope; Section11 lower, weighted-upper and full upper-sieve estimates and normalized numerical positivity are complete conditional implications; the final Goldbach assembly and manuscript presieving synchronization remain. Independent general effective mean-value and classical Mertens hypotheses remain explicit and unproved; all own weighted upper main-term deductions are complete. Earlier independent theorem scopes are unchanged. The full Section11 lower-sieve proposition p:sieveneedlower8 is a complete conditional implication, including its actual main term, uniform o(1), n-independent coefficients and mean-square error. The uniform main-term lower bound l:maintermsize8 and its joint application with the same large cutoff C are also complete conditionally. The full weighted upper main-term comparison l:wumatomakisum is a complete checked implication from the documented independent effective mean-value and Mertens inputs, with the exact printed constant and uniform retained-range quantifiers. The complete upper-sieve proposition and strict numerical comparison are proved conditionally with exact constants and uniform quantifiers. The final Goldbach assembly and manuscript presieving synchronization remain.

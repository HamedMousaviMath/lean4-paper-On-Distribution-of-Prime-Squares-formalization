# Checkpoint 1261: Primitive criterion and remaining Section9 prerequisites proved

The full primitive sum-of-two-squares criterion used in Section9 is now proved unconditionally: for n=2 mod4, n has a coprime sum-of-two-squares representation exactly when no prime3 mod4 divides n. The proof constructs a primitive representation of the odd cofactor using the checked prime-multiplication argument, then doubles it; parity excludes a common factor2. The converse uses Mathlib's already proved obstruction to -1 being a square modulo a3 mod4 prime. No external arithmetic criterion is assumed.

The source's unnumbered assertion that W(alpha) is finite for every alpha>1 is now proved across its full range, with interval integrability of the actual logarithmic kernel. The endpoint square-root singularity is handled by an integrable negative half power; nonnegativity is also proved for the complete range. This extends the earlier special-value formalization at alpha9/8.

A concrete smooth bump with inner radius1/32 and outer radius1/16 is converted to a Schwartz function. Lean verifies value1 at0, nonzero, compact support contained in(-1/8,1/8), and the source support cutoff. Thus the proof will no longer need an externally supplied test function at the final endpoint. No additional source replacement is required for these valid mathematical statements.

This checkpoint saves these prerequisite proofs separately. The next checked export specializes the legacy parameterized Section9 deductions with the proved criterion and fixed seed, and updates the source map. No source claim is promoted before that final statement review. The previously supplied manuscript edits remain in progress; no changed user source is assumed.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachPrimitiveCriterion.lean | 3 |
| GoldbachGeneralWeightedIntegral.lean | 2 |
| GoldbachFixedSmoothSeed.lean | 6 |

- `goldbach_primitive_one_mod_four_support`
- `goldbach_primitive_double_of_odd`
- `goldbach_primitive_two_squares_criterion`
- `goldbach_weighted_W_integrable_general`
- `goldbach_weighted_W_nonneg_general`
- `goldbach_fixed_smooth_seed_at_zero`
- `goldbach_fixed_smooth_seed_nonzero`
- `goldbach_fixed_smooth_seed_support`
- `goldbach_fixed_smooth_seed_compact_support`
- `goldbach_fixed_smooth_seed_tsupport_subset`
- `goldbach_smooth_seed_exists`

<!-- checkpoint-verification -->

## Verification

All 1378 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 5175-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 4488 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1380 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; all Section10 statements and the full circle-method implication are complete in the agreed conditional scope; All Section11 theorem statements, using the explicitly supplied corrected presieving replacement, are complete in the agreed conditional scope. The common-cutoff lower/upper assembly, exact constants and complete error estimates are proved; the original manuscript still needs the supplied replacements. Independent general effective mean-value and classical Mertens hypotheses remain explicit and unproved; all own weighted upper main-term deductions are complete. Earlier independent theorem scopes are unchanged. The full Section11 lower-sieve proposition p:sieveneedlower8 is a complete conditional implication, including its actual main term, uniform o(1), n-independent coefficients and mean-square error. The uniform main-term lower bound l:maintermsize8 and its joint application with the same large cutoff C are also complete conditionally. The full weighted upper main-term comparison l:wumatomakisum is a complete checked implication from the documented independent effective mean-value and Mertens inputs, with the exact printed constant and uniform retained-range quantifiers. The complete upper-sieve proposition and strict numerical comparison are proved conditionally with exact constants and uniform quantifiers. The joint Section11 estimates are proved at one cutoff. The full quantitative Goldbach theorem is proved conditionally at every large real cutoff X; the supplied presieving replacement still needs to be copied into the user manuscript.

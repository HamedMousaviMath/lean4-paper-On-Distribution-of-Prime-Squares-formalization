# Checkpoint 1229: Common arbitrarily large cutoff for the full lower sieve

The circle-method and lower-sieve estimates now permit any prescribed minimum cutoff exponent Cmin. The proof selects C=max(max(CC,CM),Cmin) in the existing major/minor assembly and verifies every earlier threshold explicitly. The cutoff and full circle estimates, selected signed remainder estimates, lower mean-square estimate and full lower-sieve application are all exported with Cmin<=C. Thus enlarging C for the main-term smoothing argument is an actual theorem, rather than an inferred monotonicity assertion. No previous Lean proof is edited and no additional analytic hypothesis is used. Both lower-sieve clauses hold for one common selected R=(log N)^C, with all coefficients still chosen before n. The quantitative main-term size and its joint application are the next step.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachLowerCutoffFreedom.lean | 5 |

- `goldbach_circle_method_cutoff_above`
- `goldbach_circle_method_above`
- `goldbach_sieve_remainders_selected_above`
- `goldbach_lower_remainder_mean_square_above`
- `goldbach_lower_sieve_complete_above`

<!-- checkpoint-verification -->

## Verification

All 1312 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 5105-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 4244 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1314 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; all Section10 statements and the full circle-method implication are complete in the agreed conditional scope; Section11 remains open. The lower-sieve endpoint is proved from independent ordinary SW/BV, raw Ren/Ghosh, one-stage Rosser-Iwaniec, interval Mertens and classical sieve-function continuity inputs. No own-paper sieve or Goldbach endpoint is assumed. The full Section11 lower-sieve proposition p:sieveneedlower8 is a complete conditional implication, including its actual main term, uniform o(1), n-independent coefficients and mean-square error. The main-term size, weighted upper main-term sum, upper sieve, numerical comparison and final Goldbach conclusion remain open.

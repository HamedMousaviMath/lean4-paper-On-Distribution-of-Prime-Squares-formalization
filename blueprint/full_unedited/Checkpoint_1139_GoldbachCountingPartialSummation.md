# Checkpoint 1139: Quantitative partial summation from actual prime-count discrepancies

Quantitative partial summation is proved for actual finite counting sums and a differentiable model with zero lower value at2. The prime at2 remains in the finite sum; no artificial lower-bound convention is assumed. The identity is derived from Mathlib Abel summation and integration by parts, with all integrability obligations proved. A unit-norm phase with derivative bounded by D transports a uniform counting discrepancy B to error at most B(1+D(U-2)). Specializing to the actual prime progression coefficient and actual Li/phi model gives the needed unweighted prime exponential-sum implication. This is an internal proved conversion, not an external weighted prime estimate.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachCountingPartialSummation.lean | 4 |

- `goldbach_counting_model_error_identity`
- `goldbach_counting_partial_error_bound`
- `goldbach_prime_weighted_count_sum`
- `goldbach_prime_progression_partial_error`

<!-- checkpoint-verification -->

## Verification

All 1206 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4997-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 3739 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1208 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; the Section10/11 analytic and sieve estimates remain open internal obligations. The rational smooth multifrequency theorem with circle transference remains an explicit independent compound hypothesis. The classical primitive sum-of-two-squares criterion is an additional explicit independent arithmetic hypothesis for Section9 reductions; it contains no own-paper conclusion and is not declared as a Lean axiom.

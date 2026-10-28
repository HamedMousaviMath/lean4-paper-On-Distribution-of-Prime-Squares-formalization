# Checkpoint 1209: Uniform completion budgets and geometry

The elementary logarithmic budgets are checked with explicit sufficient threshold C >= 2 A + 16. The squared pointwise small-modulus error summed over n < N^2 has the required N^4 log(N)^(-A) bound; the Rankin pointwise tail has the same mean-square scale. The actual hard and smooth arc separation inequalities are proved eventually for the chosen Y=N/(100 sqrt R), with all thresholds chosen before arithmetic families.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachCompletionBudgets.lean | 4 |

- `goldbach_uniform_finite_square_sum`
- `goldbach_small_completion_square_budget`
- `goldbach_far_completion_square_budget`
- `goldbach_completion_all_parameters_eventual`

<!-- checkpoint-verification -->

## Verification

All 1276 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 5069-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 4064 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1278 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; the Section10/11 analytic and sieve estimates remain open internal obligations. The rational smooth multifrequency theorem with circle transference remains an explicit independent compound hypothesis. The classical primitive sum-of-two-squares criterion is an additional explicit independent arithmetic hypothesis for Section9 reductions; it contains no own-paper conclusion and is not declared as a Lean axiom.

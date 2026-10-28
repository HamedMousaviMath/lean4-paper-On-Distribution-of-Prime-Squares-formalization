# Checkpoint 1191: Actual Rankin parameter decay with arbitrary logarithmic saving

The logarithmic-versus-power argument is proved with explicit sufficient inequalities. A general logarithmic quadratic budget gives the negative exponential Rankin saving while controlling the polynomial Euler-product factor.

For every fixed C≥1,M>0,K and t>0, the genuine parameter expression with R=x^C and Y=exp(x)/(100sqrt(R)) is proved at most x^(-t) for all sufficiently large real x. Every logarithm is evaluated with its positivity assumptions, and the numerical100 and square-root scale are retained. The threshold depends only on the fixed parameters, not on arithmetic moduli or coefficient families.

The final substitution x=log N and the actual smooth-divisor tail are next; the major-completion source statement remains open until the Fourier and arithmetic errors are assembled.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachRankinDecay.lean | 3 |

- `goldbach_eventually_log_square_budget`
- `goldbach_rankin_decay_log_budget`
- `goldbach_rankin_parameter_decay`

<!-- checkpoint-verification -->

## Verification

All 1258 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 5051-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 3992 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1260 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; the Section10/11 analytic and sieve estimates remain open internal obligations. The rational smooth multifrequency theorem with circle transference remains an explicit independent compound hypothesis. The classical primitive sum-of-two-squares criterion is an additional explicit independent arithmetic hypothesis for Section9 reductions; it contains no own-paper conclusion and is not declared as a Lean axiom.

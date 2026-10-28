# Checkpoint 1203: Printed completion geometry and logarithmic error rates

The elementary disjointness conditions are discharged for the exact printed Y=N/(100sqrt(R)), retaining the numerical100. If N≥10000,R≥1 andR³≤N, thenY≥R, the smoothing support is inside the centered half interval, and the translated supports have the required strict rational separation.

For every fixed C≥1, all these conditions are proved eventually forR=(log N)^C, with one natural threshold before all arithmetic families. A general rate lemma also proves(log N)^j/sqrt(R)≤(log N)^(-A) wheneverC≥2A+2j andlog N≥1. Thus the actual added-modulus bound has the required arbitrary logarithmic saving after choosing C large enough.

The remaining analytic estimate is the sharp-to-smoothed small-modulus comparison; exact source-model and final error assembly follow.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachCompletionParameters.lean | 3 |

- `goldbach_completion_geometry`
- `goldbach_completion_parameters_eventual`
- `goldbach_completion_log_power_rate`

<!-- checkpoint-verification -->

## Verification

All 1270 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 5063-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 4037 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1272 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; the Section10/11 analytic and sieve estimates remain open internal obligations. The rational smooth multifrequency theorem with circle transference remains an explicit independent compound hypothesis. The classical primitive sum-of-two-squares criterion is an additional explicit independent arithmetic hypothesis for Section9 reductions; it contains no own-paper conclusion and is not declared as a Lean axiom.

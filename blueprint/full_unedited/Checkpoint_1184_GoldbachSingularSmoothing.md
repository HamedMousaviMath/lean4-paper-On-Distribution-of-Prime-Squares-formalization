# Checkpoint 1184: Actual uniform singular-integral smoothing estimate

For the actual normalized seed and exact source I_U,J_(ell,W), the genuine smoothed integral differs from the genuine unsmoothed inverse integral by at most K N/sqrt(R), with K depending only on the fixed seed. The constant is selected before N,ell,R,U,W,n; all positive ell and all real n are included.

The proof substitutes the actual quadratic cutoff bound into the global smoothing lemma, proves every integral used in the subtraction is integrable, and handles the empty progression-domain case exactly. The scale R/N² is simplified without dropping ell or endpoint dependence.

The remaining clause for closing l:positiveH9 is the exact identification of the unsmoothed inverse integral with the printed positive one-variable H_ell. This identity has not become an external input. Major completion and final circle-method assembly also remain internal obligations.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachSingularSmoothing.lean | 1 |

- `goldbach_singular_smoothing_uniform`

<!-- checkpoint-verification -->

## Verification

All 1251 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 5044-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 3955 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1253 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; the Section10/11 analytic and sieve estimates remain open internal obligations. The rational smooth multifrequency theorem with circle transference remains an explicit independent compound hypothesis. The classical primitive sum-of-two-squares criterion is an additional explicit independent arithmetic hypothesis for Section9 reductions; it contains no own-paper conclusion and is not declared as a Lean axiom.

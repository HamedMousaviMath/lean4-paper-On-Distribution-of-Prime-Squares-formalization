# Checkpoint 1157: Constructed measurable source major-arc models with all-Lp regularity

The source major-arc models are now actual measurable functions on the circle, constructed as finite indicators of the exact source major balls times the genuine local-coordinate integrals. A general localization theorem proves their precise source value on each arc using the checked pairwise disjointness. Uniform Euclidean bounds prove membership in every Lp, including infinity; this is not a measurable-model hypothesis. The square model has the exact Gauss coefficient and norm at most N/log2 on the major set. The progression model has the exact Upsilon/phi coefficient and strict source J integral. All quotient representatives, boundary values, and finite model sums are explicit.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachCircleMajorModels.lean | 8 |

- `goldbachArcModel_stronglyMeasurable`
- `goldbachArcModel_norm_bound`
- `goldbachArcModel_memLp`
- `goldbachArcModel_on_arc`
- `goldbach_square_model_norm_euclidean`
- `goldbachSquareMajorModel_memLp`
- `goldbachProgressionMajorModel_memLp`
- `goldbachSquareMajorModel_norm_on_major`

<!-- checkpoint-verification -->

## Verification

All 1224 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 5015-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 3834 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1226 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; the Section10/11 analytic and sieve estimates remain open internal obligations. The rational smooth multifrequency theorem with circle transference remains an explicit independent compound hypothesis. The classical primitive sum-of-two-squares criterion is an additional explicit independent arithmetic hypothesis for Section9 reductions; it contains no own-paper conclusion and is not declared as a Lean axiom.

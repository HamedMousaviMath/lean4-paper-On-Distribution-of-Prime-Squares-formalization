# Checkpoint 1155: Exact source major-arc geometry measure and disjointness

The major set is exactly the complement of the already formalized source minor set and equals the finite union of the source closed balls of uniform radius R/N². Its measurability, rational-centre cardinality at most4R² and normalized Haar measure at most8R³/N² are proved. Exact real lifts turn circle ball membership into the integer-shift inequalities used in the earlier rational separation theorem. Consequently the source major balls are pairwise disjoint once2R³<N². A single eventual threshold proves this separation and radius<1/2 for R=(log N)^C and every fixed C≥0. No arc, wrap-around or measure convention is assumed.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachMajorArcGeometry.lean | 10 |

- `goldbachMajorArcs_measurable`
- `mem_goldbachMajorArcs`
- `goldbach_major_arcs_union`
- `goldbach_circle_volume_eq_haar`
- `goldbach_major_ball_measure`
- `goldbach_source_centres_card`
- `goldbach_major_arcs_measure`
- `goldbach_circle_ball_real_lift`
- `goldbach_major_balls_disjoint`
- `goldbach_major_geometry_eventual`

<!-- checkpoint-verification -->

## Verification

All 1222 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 5013-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 3814 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1224 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; the Section10/11 analytic and sieve estimates remain open internal obligations. The rational smooth multifrequency theorem with circle transference remains an explicit independent compound hypothesis. The classical primitive sum-of-two-squares criterion is an additional explicit independent arithmetic hypothesis for Section9 reductions; it contains no own-paper conclusion and is not declared as a Lean axiom.

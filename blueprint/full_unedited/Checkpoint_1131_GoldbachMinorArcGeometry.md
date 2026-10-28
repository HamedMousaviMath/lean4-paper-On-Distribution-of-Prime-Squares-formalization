# Checkpoint 1131: Exact minor-arc region and rescaling between annular scales

The source minor-arc region is now an explicit measurable subset of the circle: the complement of the closed major arcs of uniform radius R/N² about reduced rational centres with denominator at most R. Its definition using all rational lifts is proved equivalent to the existing finite source-centre definition. Circle distance is bounded by the distance between any real lifts. These facts give a proved scale transfer: membership in the source minor arcs at scale N implies the annular Ren/Ghosh exclusion at every scale 1 ≤ m ≤ N with parameter R(m/N)². The denominator-dependent annular exclusion and all integer lifts are covered explicitly. No prime estimate is introduced as an independent hypothesis.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachMinorArcGeometry.lean | 5 |

- `goldbachMinorArcs_measurable`
- `goldbach_minor_arcs_source_centres`
- `goldbach_circle_distance_le_real`
- `goldbach_minor_arcs_smaller_annular`
- `goldbach_minor_arcs_rescale`

<!-- checkpoint-verification -->

## Verification

All 1198 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4989-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 3705 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1200 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; the Section10/11 analytic and sieve estimates remain open internal obligations. The rational smooth multifrequency theorem with circle transference remains an explicit independent compound hypothesis. The classical primitive sum-of-two-squares criterion is an additional explicit independent arithmetic hypothesis for Section9 reductions; it contains no own-paper conclusion and is not declared as a Lean axiom.

# Checkpoint 1156: Measurable source coordinates and actual Euclidean model bounds

A canonical measurable local circle coordinate is constructed at every rational centre. Its real absolute value is exactly the circle distance, it lies in[-1/2,1/2), and it reconstructs the original circle point. The actual square and linear logarithmic integrals are strongly measurable in frequency, by the Bochner parameter-integral theorem. The strict source linear integral inherits this regularity through its proved clamping identity. Their uniform norm bounds are proved from the actual1/log weight: |I_U|≤U/log2 and |J_ell,W|≤W/log2 in the required range. No abstract Euclidean model, measurable representative, or size estimate is assumed.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachMajorModelRegularity.lean | 12 |

- `goldbachArcCoordinate_measurable`
- `goldbachArcCoordinate_coe`
- `goldbachArcCoordinate_bounds`
- `goldbachArcCoordinate_abs`
- `goldbachArcCoordinate_reconstruct`
- `goldbachSquareIntegral_stronglyMeasurable`
- `goldbachLinearIntegral_stronglyMeasurable`
- `goldbachLinearSourceIntegral_stronglyMeasurable`
- `goldbach_phase_log_weight_bound`
- `goldbachSquareIntegral_norm`
- `goldbachLinearIntegral_norm`
- `goldbachLinearSourceIntegral_norm`

<!-- checkpoint-verification -->

## Verification

All 1223 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 5014-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 3826 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1225 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; the Section10/11 analytic and sieve estimates remain open internal obligations. The rational smooth multifrequency theorem with circle transference remains an explicit independent compound hypothesis. The classical primitive sum-of-two-squares criterion is an additional explicit independent arithmetic hypothesis for Section9 reductions; it contains no own-paper conclusion and is not declared as a Lean axiom.

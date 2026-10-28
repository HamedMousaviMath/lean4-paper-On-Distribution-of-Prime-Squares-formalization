# Checkpoint 1158: Full SW-BV bounds for the constructed exact circle models

The completed actual real-frequency SW and BV estimates are transported to the constructed source circle models. At every point of the exact source major set, the selected local coordinate reconstructs that point with its canonical reduced numerator and denominator. SW therefore bounds the actual square polynomial minus its circle model uniformly. BV bounds the sum of the actual progression-minus-model norms over the entire source coefficient family, with independent real prime cutoffs and all source ranges. All constants and thresholds precede the arithmetic/cutoff data, and the active ell scales are proved at least2 for model integrability. No arc matching, choice of rational approximant, or global model comparison remains assumed.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachCircleMajorEstimates.lean | 2 |

- `goldbach_square_circle_major_sw`
- `goldbach_linear_circle_major_bv`

<!-- checkpoint-verification -->

## Verification

All 1225 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 5016-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 3836 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1227 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; the Section10/11 analytic and sieve estimates remain open internal obligations. The rational smooth multifrequency theorem with circle transference remains an explicit independent compound hypothesis. The classical primitive sum-of-two-squares criterion is an additional explicit independent arithmetic hypothesis for Section9 reductions; it contains no own-paper conclusion and is not declared as a Lean axiom.

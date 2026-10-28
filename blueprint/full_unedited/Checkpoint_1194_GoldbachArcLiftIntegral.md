# Checkpoint 1194: Exact arc-lift Fourier coefficients and Euclidean energy

A genuine real-frequency function supported in|gamma|<1/2 is lifted to the source circle using the actual centered coordinate. The circle integral is proved equal to the real-line integral by translation invariance and the fundamental-domain measure equivalence; no periodization identity is assumed.

The exact Fourier coefficient of a translated lift is proved equal to exp(-2pi i n r) times the actual Euclidean coefficient. The circle L2 energy is also proved exactly equal to the real-line energy. Bounded strongly measurable source functions are proved to give circle MemLp functions at every exponent.

These identities provide the exact normalization and phase needed for the remaining major-model Fourier estimates, including wrapped arcs.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachArcLiftIntegral.lean | 5 |

- `goldbach_arc_coordinate_real_shift`
- `goldbach_arc_lift_integral`
- `goldbach_arc_lift_fourier_integral`
- `goldbach_arc_lift_energy`
- `goldbach_arc_lift_memLp`

<!-- checkpoint-verification -->

## Verification

All 1261 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 5054-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 4000 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1263 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; the Section10/11 analytic and sieve estimates remain open internal obligations. The rational smooth multifrequency theorem with circle transference remains an explicit independent compound hypothesis. The classical primitive sum-of-two-squares criterion is an additional explicit independent arithmetic hypothesis for Section9 reductions; it contains no own-paper conclusion and is not declared as a Lean axiom.

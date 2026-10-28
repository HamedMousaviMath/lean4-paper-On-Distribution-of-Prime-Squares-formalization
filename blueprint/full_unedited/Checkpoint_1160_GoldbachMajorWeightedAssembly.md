# Checkpoint 1160: Weighted source coefficient identity and exact major-arc budget

The weighted progression major model is constructed from the actual source models and proved to lie in every Lp space on the circle. For coefficients of norm at most one, its difference from the actual weighted prime polynomial is bounded by the sum of the individual progression error norms.

The source sum of weighted major-arc Fourier integrals is proved exactly equal to the Fourier integral of the two weighted factors. All finite sum exchanges and integrability conditions are supplied. The final numerical identity combines the major-arc measure bound8R³/N² with the SW loss N(log N)^(-(A+6)/2), the BV loss N²(log N)^(-(A+3C)/2), and the proved progression-energy bound(256/log2)N²(log N)^6. It yields an explicit constant times N⁴(log N)^(-A). No own-paper endpoint is an input.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachMajorWeightedAssembly.lean | 5 |

- `goldbachWeightedProgressionMajorModel_memLp`
- `goldbach_weighted_major_error_le_sum`
- `goldbach_major_weighted_coefficient_identity`
- `goldbach_major_square_log_identity`
- `goldbach_major_mean_square_budget`

<!-- checkpoint-verification -->

## Verification

All 1227 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 5018-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 3845 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1229 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; the Section10/11 analytic and sieve estimates remain open internal obligations. The rational smooth multifrequency theorem with circle transference remains an explicit independent compound hypothesis. The classical primitive sum-of-two-squares criterion is an additional explicit independent arithmetic hypothesis for Section9 reductions; it contains no own-paper conclusion and is not declared as a Lean axiom.

# Checkpoint 1180: Exact Fubini identity for positive Fourier kernel averages

Fubini is proved for a genuine Schwartz cutoff and every integrable real weight on a product-space measure. The actual Euclidean frequency integral equals the weighted average of the cutoff inverse transform at the sum frequency. Absolute integrability of the joint integrand is proved from the product of the L1 norms.

If the weight is nonnegative and the cutoff inverse transform is real nonnegative, the resulting actual Fourier integral is real nonnegative. This is the analytic mechanism for positivity of H_(ell,R). It is proved from ordinary integration and Fourier inversion, not postulated. Substitution of the exact paper integrals and the quantitative comparison remain next.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachPositiveFourierAverage.lean | 2 |

- `goldbach_cutoff_fourier_fubini`
- `goldbach_positive_cutoff_fourier_average`

<!-- checkpoint-verification -->

## Verification

All 1247 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 5040-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 3943 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1249 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; the Section10/11 analytic and sieve estimates remain open internal obligations. The rational smooth multifrequency theorem with circle transference remains an explicit independent compound hypothesis. The classical primitive sum-of-two-squares criterion is an additional explicit independent arithmetic hypothesis for Section9 reductions; it contains no own-paper conclusion and is not declared as a Lean axiom.

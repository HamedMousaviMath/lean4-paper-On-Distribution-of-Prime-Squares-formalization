# Checkpoint 1182: Global Euclidean L1 and uniform singular-integral bounds

The genuine Euclidean product I_U J_(ell,W) is proved absolutely integrable over the full real frequency line. Splitting at1/N² and evaluating both improper tails gives an explicit uniform L1 bound C N/ell, where C=2/(log2)²+4D and D is the previously proved absolute decay constant.

The exact eta_N-squared singular-integral integrand is separately proved integrable and is dominated in modulus by the Euclidean product. Consequently |H_(ell,R)(n;U,W)|≤C N for every real n and all positive ell, retaining U,W and the exact strict source domain. The empty-domain branch is included. This discharges the uniform kernel bound needed by the arithmetic tail in major completion.

The O(N/sqrt(R)) comparison with the printed H_ell and the full completed major-arc error still remain internal obligations.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachSingularIntegralNorm.lean | 5 |

- `goldbachEuclideanL1Constant_pos`
- `goldbach_euclidean_product_integrable`
- `goldbach_singular_integrand_norm`
- `goldbach_singular_integrand_integrable`
- `goldbach_singular_integral_norm`

<!-- checkpoint-verification -->

## Verification

All 1249 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 5042-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 3952 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1251 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; the Section10/11 analytic and sieve estimates remain open internal obligations. The rational smooth multifrequency theorem with circle transference remains an explicit independent compound hypothesis. The classical primitive sum-of-two-squares criterion is an additional explicit independent arithmetic hypothesis for Section9 reductions; it contains no own-paper conclusion and is not declared as a Lean axiom.

# Checkpoint 1167: Actual Euclidean product bounds and both improper tails

The source linear integral is bounded by N²/(ell log2), uniformly in W, using the actual clamped strict-domain integral. Consequently the genuine product I_U(gamma) J_ell,W(gamma) has the flat bound N³/(ell(log2)²) and the decay bound(D/ell) abs(gamma)^(-3/2), where D=(2 quadraticIntegralConstant/log2)/(pi log2)>0.

For every c>0 and either frequency direction sigma with abs(sigma)=1, the actual complex product at sigma*gamma is proved integrable on(c,infinity). Its norm integral is bounded by2D/(ell sqrt c). This is obtained by domination with the actual integrable rpow tail and evaluation of that improper integral. No Fourier-decay, integrability or tail endpoint is an external assumption. These establish the Euclidean tails needed in smoothing; the actual cutoff replacement and full circle-method completion remain open.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachEuclideanProduct.lean | 6 |

- `goldbachEuclideanDecayConstant_pos`
- `goldbachLinearSourceIntegral_norm_scale`
- `goldbach_euclidean_product_flat`
- `goldbach_inverse_sqrt_power`
- `goldbach_euclidean_product_decay`
- `goldbach_euclidean_product_tail`

<!-- checkpoint-verification -->

## Verification

All 1234 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 5027-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 3879 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1236 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; the Section10/11 analytic and sieve estimates remain open internal obligations. The rational smooth multifrequency theorem with circle transference remains an explicit independent compound hypothesis. The classical primitive sum-of-two-squares criterion is an additional explicit independent arithmetic hypothesis for Section9 reductions; it contains no own-paper conclusion and is not declared as a Lean axiom.

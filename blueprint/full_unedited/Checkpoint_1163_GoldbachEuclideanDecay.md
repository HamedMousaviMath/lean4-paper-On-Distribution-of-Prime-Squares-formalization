# Checkpoint 1163: Genuine reciprocal-log Euclidean integral decay

The actual reciprocal-log weight is proved antitone on every source interval. Mathlib's general vector-valued second mean value theorem, proved in the pinned dependency, transfers the existing unweighted quadratic oscillatory bound to the genuine source integral: norm I_U(gamma)≤(2 quadraticIntegralConstant/log2)/sqrt(abs gamma).

The actual linear exponential primitive is differentiated and integrated exactly. This gives norm of its interval integral≤1/(pi abs beta), then norm J_U(beta)≤1/(pi log2 abs beta). The strict-domain source integral is identified with its clamped endpoint and satisfies norm J_ell,W(gamma)≤1/(pi log2 ell abs gamma). No van der Corput or Fourier-decay assertion is assumed externally. The results are uniform for every real cutoff in the printed range. The quantitative arithmetic bounds, smoothing assembly and full l:circmethod remain open.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachEuclideanDecay.lean | 6 |

- `goldbach_inverse_log_antitone`
- `goldbach_quadratic_interval_decay`
- `goldbachSquareIntegral_decay`
- `goldbach_linear_interval_decay`
- `goldbachLinearIntegral_decay`
- `goldbachLinearSourceIntegral_decay`

<!-- checkpoint-verification -->

## Verification

All 1230 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 5023-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 3858 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1232 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; the Section10/11 analytic and sieve estimates remain open internal obligations. The rational smooth multifrequency theorem with circle transference remains an explicit independent compound hypothesis. The classical primitive sum-of-two-squares criterion is an additional explicit independent arithmetic hypothesis for Section9 reductions; it contains no own-paper conclusion and is not declared as a Lean axiom.

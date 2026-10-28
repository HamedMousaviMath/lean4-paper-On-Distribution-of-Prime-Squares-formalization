# Checkpoint 1178: All source cutoff bounds from the genuine seed

The normalized autocorrelation cutoff is proved real and even, and its modulus is at most1. The latter follows by integrating the elementary inequality2|uv|≤u²+v² and translation invariance, so it does not require nonnegativity of the original seed.

Evenness gives eta'(0)=0. Bounds on the second derivative of the actual Schwartz cutoff and two applications of the mean value theorem give the uniform quadratic estimate. In particular there exists a positive constant K depending only on the fixed seed such that |1-eta(x)²|≤K min(1,|x|²) for every real x. This is precisely the source cutoff bound before the singular-integral lemma, with its scale dependence retained through the proved dilation formula.

The cutoff properties are now proved from the source construction. They are not new independent hypotheses. The actual singular integral still needs its Fourier inversion, nonnegativity and quantitative comparison, followed by major completion and final assembly.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachCutoffBounds.lean | 8 |

- `goldbach_eta_real`
- `goldbach_eta_even`
- `goldbach_autocorrelation_norm`
- `goldbach_eta_norm_le_one`
- `goldbach_eta_deriv_zero`
- `goldbach_schwartz_derivative_difference`
- `goldbach_eta_quadratic`
- `goldbach_eta_square_cutoff_bound`

<!-- checkpoint-verification -->

## Verification

All 1245 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 5038-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 3939 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1247 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; the Section10/11 analytic and sieve estimates remain open internal obligations. The rational smooth multifrequency theorem with circle transference remains an explicit independent compound hypothesis. The classical primitive sum-of-two-squares criterion is an additional explicit independent arithmetic hypothesis for Section9 reductions; it contains no own-paper conclusion and is not declared as a Lean axiom.

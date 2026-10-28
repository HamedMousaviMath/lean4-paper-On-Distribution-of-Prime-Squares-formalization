# Checkpoint 1185: Exact quadratic density Fourier identity with all integrability conditions

The one-variable density associated with u²+a v is constructed as the actual affine average a^(-1) integral f(u)g((x-u²)/a) du. For every positive real a and arbitrary integrable measurable f,g, its joint integrand and the resulting density are proved globally integrable.

Its genuine Fourier transform is proved equal to the product of the quadratic transform of f and the scaled linear transform of g. The affine change of variables, the scale factor a, and the Fubini integrability are all proved explicitly. This provides the exact analytic route to the printed H_ell, rather than assuming the desired inversion identity.

The source logarithmic densities, pointwise continuity and the final inverse identity are next. No new external analytic input is introduced.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachQuadraticDensity.lean | 5 |

- `goldbach_affine_integral`
- `goldbach_forward_fourier_integral`
- `goldbach_quadratic_density_joint`
- `goldbach_quadratic_average_integrable`
- `goldbach_quadratic_average_fourier`

<!-- checkpoint-verification -->

## Verification

All 1252 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 5045-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 3960 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1254 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; the Section10/11 analytic and sieve estimates remain open internal obligations. The rational smooth multifrequency theorem with circle transference remains an explicit independent compound hypothesis. The classical primitive sum-of-two-squares criterion is an additional explicit independent arithmetic hypothesis for Section9 reductions; it contains no own-paper conclusion and is not declared as a Lean axiom.

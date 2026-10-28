# Checkpoint 1223: Presieve Euler mass, exact scales and uniform error decay

The outer coefficient mass is bounded for the actual square-free divisor support. The proof first derives the prime-product expression from multiplicativity on supported square-free integers; no stronger global multiplicativity hypothesis is used. Injectivity of the prime-factor set on square-free integers then embeds the divisor sum into a sum over subsets of the outer prime set. Expanding the Euler product gives
\[
 M=\sum_d |u(d)|g(d)\leq\prod_{p\in\mathfrak P_1}(1+g(p)),\qquad
 \frac{M}{V_1}\leq V_1^{-2}.
\]
Every factor of V1 is strictly positive. The estimate uses only0<=g(p)<1 and |u(d)|<=1; the outer weights may have either sign.

Given the dimension product bound at w=2 and log(z)<=A*log(N), the inverse outer Euler product is at most
\[
 K_2(\log N)^\kappa,\qquad
 K_2=(1+K/\log2)(A/\log2)^\kappa.
\]
The finite preliminary error therefore has a uniform logarithmic majorant independent of the density function.

Write t=log(log(N)), D0=exp(t^3), and use preliminary sifting limit exp(C*t)+1. Lean proves
\[
 s_0\geq\frac{t^2}{C+1}
\]
for t>=1, proves s0 tends to infinity, and proves D0 eventually exceeds that sifting limit. Gaussian decay against every fixed exponential-linear factor and power of t is proved from Mathlib's exponential asymptotics. Consequently the preliminary error K0*exp(-c*s0) absorbs every fixed power of log(N).

If D1 is at least exp(C*t)+1 eventually, it tends to infinity. For every delta>0, the outer error K1*(log(D1))^(-delta) tends to zero. Combining these deductions proves the exact common error rate used in the next assembly:
\[
 K_1(\log D_1)^{-\delta}
 +K_0 e^{-c s_0}\bigl(K_2(\log N)^\kappa\bigr)^2\longrightarrow0.
\]
All these arithmetic and limit deductions are proved internally. The independent classical one-stage coefficient theorem is not used as an input to this milestone. The next milestone connects its two explicit interfaces to these bounds and proves the corrected full presieving implication. The original weaker manuscript statement remains unclaimed, with proposed replacements saved separately.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachPresieveDecay.lean | 11 |
| GoldbachPresieveEulerMass.lean | 5 |

- `goldbach_presieve_gaussian_decay`
- `goldbach_presieve_polylog_decay`
- `goldbach_presieve_preliminary_ratio`
- `goldbach_presieve_preliminary_error_bound`
- `goldbach_presieve_preliminary_s_tendsto`
- `goldbach_presieve_preliminary_level_eventually`
- `goldbach_presieve_preliminary_absorption`
- `goldbach_presieve_outer_level_tendsto`
- `goldbach_presieve_outer_error_tendsto`
- `goldbach_presieve_total_error_tendsto`
- `goldbach_presieve_uniform_error_tendsto`
- `goldbach_presieve_density_prime_product`
- `goldbach_presieve_outer_mass`
- `goldbach_presieve_outer_product`
- `goldbach_presieve_outer_mass_ratio`
- `goldbach_presieve_inverse_polylog`

<!-- checkpoint-verification -->

## Verification

All 1302 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 5095-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 4195 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1304 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; all Section10 statements and the full circle-method implication are complete in the agreed conditional scope; Section11 remains open. The rational smooth multifrequency theorem with circle transference remains an explicit independent compound hypothesis. The classical primitive sum-of-two-squares criterion is an additional explicit independent arithmetic hypothesis for Section9 reductions; it contains no own-paper conclusion and is not declared as a Lean axiom.

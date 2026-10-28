# Checkpoint 1228: Explicit archimedean and arithmetic product lower bounds

The lower-bound ingredients now include a kernel-checked explicit archimedean integral estimate and quantitative bounds for the actual local products. For64<=n<=N^2, the interval[sqrt(n)/4,sqrt(n)/2] lies inside the original integration domain. On it, the integrand is at least1/(2(log N)^2). Integrability, global nonnegativity, restriction monotonicity and the exact interval measure are proved, yielding H1(n)>=sqrt(n)/(8(log N)^2). The singular integral is the original one; no artificial substitute main term is introduced.

For every prime p>=7, the unrestricted arithmetic local factor is at least1-2/(p-3); the prime5 factor is at least1/2. The original arithmetic factor is exactly24 times the product of these real factors. From the already recorded general interval Mertens input, Lean proves its lower bound12/((1+K/log2)(log(R+1)/log2)^2). It also proves the uniform inverse bound Theta_n(z)^(-1)<=(1+K/log2)(log z/log2)^2 for the actual lower Euler product. These estimates hold uniformly in n. No new external analytic input is used. Smoothing absorption, a C-independent logarithmic exponent, and common-cutoff compatibility remain to be assembled before closing l:maintermsize8.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachArchimedeanLower.lean | 5 |
| GoldbachLowerProductBounds.lean | 6 |

- `goldbach_lower_arch_integrand_nonneg`
- `goldbach_lower_arch_integrand_integrable`
- `goldbach_lower_arch_real`
- `goldbach_lower_arch_interval`
- `goldbach_archimedean_lower`
- `goldbach_unrestricted_local_real_positive`
- `goldbach_unrestricted_local_majorant`
- `goldbach_unrestricted_local_five`
- `goldbach_lower_arithmetic_real_product`
- `goldbach_lower_theta_inverse`
- `goldbach_lower_arithmetic_polylog`

<!-- checkpoint-verification -->

## Verification

All 1311 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 5104-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 4239 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1313 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; all Section10 statements and the full circle-method implication are complete in the agreed conditional scope; Section11 remains open. The lower-sieve endpoint is proved from independent ordinary SW/BV, raw Ren/Ghosh, one-stage Rosser-Iwaniec, interval Mertens and classical sieve-function continuity inputs. No own-paper sieve or Goldbach endpoint is assumed. The full Section11 lower-sieve proposition p:sieveneedlower8 is a complete conditional implication, including its actual main term, uniform o(1), n-independent coefficients and mean-square error. The main-term size, weighted upper main-term sum, upper sieve, numerical comparison and final Goldbach conclusion remain open.

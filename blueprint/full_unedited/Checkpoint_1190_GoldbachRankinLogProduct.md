# Checkpoint 1190: Unconditional logarithmic Rankin Euler product and finite tail bound

The local Rankin bounds are assembled into a proved logarithmic Euler-product bound. The small real-power factor satisfies p^(-1+sigma)≤exp(1)/p whenever sigma≥0 and sigma log R≤1. Bernoulli's inequality then bounds each factor by a fixed integer power of1+1/p.

The already-proved elementary prime-product estimate gives a fixed natural exponent K such that the full divisor Rankin sum is at most(M log(2R))^K, uniformly in the supporting integer and its prime-power exponents. Here M=12+2/log3 is explicit. Combining this with the finite Rankin reduction gives the actual tail bound Y^(-sigma)(M log(2R))^K for every finite divisor subset with q>Y. No Mertens theorem, PNT or extra distribution input is assumed.

The eventual source-parameter saving and the major-arc Fourier assembly remain to be completed.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachRankinLogProduct.lean | 5 |

- `goldbachPrimeProductConstant_pos`
- `goldbach_rankin_prime_rpow`
- `goldbach_prime_subset_inclusive_log`
- `goldbach_rankin_euler_log`
- `goldbach_rankin_tail_log_bound`

<!-- checkpoint-verification -->

## Verification

All 1257 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 5050-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 3989 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1259 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; the Section10/11 analytic and sieve estimates remain open internal obligations. The rational smooth multifrequency theorem with circle transference remains an explicit independent compound hypothesis. The classical primitive sum-of-two-squares criterion is an additional explicit independent arithmetic hypothesis for Section9 reductions; it contains no own-paper conclusion and is not declared as a Lean axiom.

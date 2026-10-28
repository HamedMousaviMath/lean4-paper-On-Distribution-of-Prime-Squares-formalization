# Checkpoint 1188: Exact Rankin tail reduction and positive divisor Euler product

The positive Rankin weight tau(q)^11 q^(-1+sigma) is proved multiplicative for every real sigma. Its local prime-power value is computed exactly, and the finite divisor sum is proved equal to the genuine prime-by-prime Euler product.

For every positive sigma,Y and every finite subset of the positive divisors of a nonzero integer, the portion with q>Y is bounded by Y^(-sigma) times that exact Euler product. The inequality is proved from real powers, with all positivity conditions retained. The factorial-cube support already proved for the actual smooth coefficients is a direct admissible specialization.

This proves the algebraic Rankin reduction required by major completion. The uniform logarithmic estimate for the Euler product and the actual major-arc completion still remain to be assembled. The full arithmetic and singular-integral source lemmas remain proved.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachRankinEuler.lean | 6 |

- `goldbach_rankin_weight_nonnegative`
- `goldbach_rankin_weight_multiplicative`
- `goldbach_rankin_weight_prime_power`
- `goldbach_rankin_divisor_euler`
- `goldbach_rankin_pointwise`
- `goldbach_finite_rankin_euler_bound`

<!-- checkpoint-verification -->

## Verification

All 1255 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 5048-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 3981 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1257 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; the Section10/11 analytic and sieve estimates remain open internal obligations. The rational smooth multifrequency theorem with circle transference remains an explicit independent compound hypothesis. The classical primitive sum-of-two-squares criterion is an additional explicit independent arithmetic hypothesis for Section9 reductions; it contains no own-paper conclusion and is not declared as a Lean axiom.

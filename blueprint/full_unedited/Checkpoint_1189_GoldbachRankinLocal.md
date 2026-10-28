# Checkpoint 1189: Uniform local Rankin Euler-factor bound

A uniform finite geometric estimate is proved, and the polynomial exponent factor is absorbed using the already-proved elementary exponential bound. This gives one positive absolute constant C such that every local Rankin factor satisfies sum_(j=0)^J (j+1)^11 p^(j(-1+sigma))≤1+C p^(-1+sigma), simultaneously for every prime p, sigma≤1/2 and every exponent cutoff J.

The proof uses an explicit auxiliary ratio2^(1/44), proves the resulting geometric ratio is below1, and retains the exact constant term1. That last point is essential for a logarithmic prime product rather than a factor growing once for each prime. No prime-distribution theorem or new external input is used.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachRankinLocal.lean | 3 |

- `goldbach_geometric_partial_bound`
- `goldbach_polynomial_local_bound`
- `goldbach_rankin_local_uniform`

<!-- checkpoint-verification -->

## Verification

All 1256 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 5049-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 3984 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1258 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; the Section10/11 analytic and sieve estimates remain open internal obligations. The rational smooth multifrequency theorem with circle transference remains an explicit independent compound hypothesis. The classical primitive sum-of-two-squares criterion is an additional explicit independent arithmetic hypothesis for Section9 reductions; it contains no own-paper conclusion and is not declared as a Lean axiom.

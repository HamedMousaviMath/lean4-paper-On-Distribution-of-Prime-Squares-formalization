# Checkpoint 1145: Precise ordinary prime-count SW-BV inputs and elementary budgets

Precise independent general SW and BV interfaces are recorded only for actual ordinary unweighted prime counts relative to the actual logarithmic integral divided by phi(h). Their complex discrepancy is proved equal to the usual real absolute error. SW is uniform in the reduced residue, all endpoints up to N and every fixed logarithmic modulus range. BV has the classical endpoint maximum and an unweighted modulus sum up to sqrt(X)(log X)^(-L), with an honest error majorant for the actual counts. Neither interface mentions a quadratic phase, the paper's coefficient family or a circle-method conclusion. The external theorems remain unproved propositions, not Lean axioms. The source square approximation is reduced numerically to R+(1+4*pi)R² times its ordinary count discrepancy; the necessary logarithmic power identity and eventual radius-error absorption are proved. The full SW square application is the next internal deduction. The fixed-q lcm bound permits ordinary BV directly, with no extra divisor-weighted distribution input.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachRawPrimeDistribution.lean | 4 |

- `goldbach_prime_count_discrepancy_real`
- `goldbach_major_radius_eventual_budget`
- `goldbach_square_major_numeric`
- `goldbach_major_log_product`

<!-- checkpoint-verification -->

## Verification

All 1212 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 5003-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 3771 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1214 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; the Section10/11 analytic and sieve estimates remain open internal obligations. The rational smooth multifrequency theorem with circle transference remains an explicit independent compound hypothesis. The classical primitive sum-of-two-squares criterion is an additional explicit independent arithmetic hypothesis for Section9 reductions; it contains no own-paper conclusion and is not declared as a Lean axiom.

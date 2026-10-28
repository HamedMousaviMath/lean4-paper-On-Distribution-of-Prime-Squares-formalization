# Checkpoint 1133: Explicit logarithmic parameters for the actual minor-arc prime saving

The logarithmic parameters are explicit. For target saving t > 0, set K=t+2, H=N(log N)^(-K), and take any C ≥ 6t+4d+8, where d is the logarithmic exponent in the existing raw Ren/Ghosh input. The rescaled annular radius is exactly (log N)^(C-2K). Its quarter-power saving absorbs both d and the target t. The small-scale term H log N equals N(log N)^(-t-1). Once the elementary eventual scale and square-root budgets hold, the actual prime polynomial has the uniform bound Z N(log N)^(-t), where Z=(2P+3)/log 2 and P is the sum of the proved Ren/Ghosh constants. Every C above the threshold is allowed. No own endpoint estimate is an assumption.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachMinorLogParameters.lean | 5 |

- `goldbachMinorPrimeConstant_pos`
- `goldbach_log_minor_radius_identity`
- `goldbach_log_minor_annular_budget`
- `goldbach_log_minor_small_cutoff`
- `goldbach_prime_minor_log_parameters`

<!-- checkpoint-verification -->

## Verification

All 1200 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4991-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 3713 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1202 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; the Section10/11 analytic and sieve estimates remain open internal obligations. The rational smooth multifrequency theorem with circle transference remains an explicit independent compound hypothesis. The classical primitive sum-of-two-squares criterion is an additional explicit independent arithmetic hypothesis for Section9 reductions; it contains no own-paper conclusion and is not declared as a Lean axiom.

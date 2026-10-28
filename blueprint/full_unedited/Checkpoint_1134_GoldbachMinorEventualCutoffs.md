# Checkpoint 1134: Eventual cutoff and proper-prime-power budgets without extra inputs

All numeric assumptions needed by the prime minor-arc estimate are now proved eventually. The proof uses the formal logarithm-versus-positive-power limit with explicit constants. For every fixed target t and radius exponent C, a natural threshold N₀ ≥ 4 works simultaneously for log N ≥ 1, H=N(log N)^(-(t+2)) ≥ max(4,startingScale,exp 1), (log N)^(4C) ≤ H/2, and sqrt(N) log N ≤ N(log N)^(-t). The threshold is independent of the real prime cutoff U, the circle frequency, the progression cutoff W, the coefficient family, and the residue classes. This discharges the finite-scale and proper-prime-power budgets without introducing a new analytic hypothesis.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachMinorEventualCutoffs.lean | 2 |

- `goldbach_minor_real_eventual_budgets`
- `goldbach_minor_eventual_numeric_parameters`

<!-- checkpoint-verification -->

## Verification

All 1201 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4992-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 3715 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1203 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; the Section10/11 analytic and sieve estimates remain open internal obligations. The rational smooth multifrequency theorem with circle transference remains an explicit independent compound hypothesis. The classical primitive sum-of-two-squares criterion is an additional explicit independent arithmetic hypothesis for Section9 reductions; it contains no own-paper conclusion and is not declared as a Lean axiom.

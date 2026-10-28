# Checkpoint 1205: Weighted small-modulus smoothing error

The divisor bound and the elementary harmonic estimate give the actual finite sum over q <= R of tau(q)^11/q at most K R^(1/4)(1+log R). Applying the proved arithmetic family inequality to the actual difference of the sharp and smooth singular integrals yields a uniform bound K N (log N)^2 (1+log R) / R^(1/4). The constants are fixed before all source arithmetic families. This slightly weaker power of R still yields every prescribed logarithmic saving by increasing the chosen C.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachSmallSmoothing.lean | 2 |

- `goldbach_divisor_harmonic_initial_sum`
- `goldbach_small_smoothing_uniform`

<!-- checkpoint-verification -->

## Verification

All 1272 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 5065-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 4046 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1274 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; the Section10/11 analytic and sieve estimates remain open internal obligations. The rational smooth multifrequency theorem with circle transference remains an explicit independent compound hypothesis. The classical primitive sum-of-two-squares criterion is an additional explicit independent arithmetic hypothesis for Section9 reductions; it contains no own-paper conclusion and is not declared as a Lean axiom.

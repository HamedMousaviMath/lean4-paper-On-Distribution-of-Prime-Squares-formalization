# Checkpoint 1193: Actual weighted arithmetic-family Rankin tail

The source Rankin saving is now applied to the genuine arithmetic-family tail weighted by the actual H_(ell,R). For every desired t>0 and C≥1, one threshold is chosen before all real L,V,B cutoffs, all coprime residues, all bounded complex coefficients, U,W, supporting smooth divisor sets and output integers n.

The proved O(N) bound for H and the full source harmonic/coefficient estimate give the actual tail norm at most(9 exp(2) C_H) N (log N)^(-t). The two logarithmic powers in the harmonic sum are explicitly absorbed by choosing the Rankin saving t+2. Positive indices and the exact strict real family bounds are retained; empty progression domains are already included in the H bound.

This closes the weighted arithmetic tail component of major completion. The full major-completion source statement still awaits the sharp small-modulus Fourier identity, its smoothing comparison and the disjoint added-modulus L2 estimate. No new external hypothesis is introduced.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachRankinArithmeticTail.lean | 2 |

- `goldbachArithmeticTailConstant_pos`
- `goldbach_source_rankin_arithmetic_tail`

<!-- checkpoint-verification -->

## Verification

All 1260 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 5053-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 3995 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1262 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; the Section10/11 analytic and sieve estimates remain open internal obligations. The rational smooth multifrequency theorem with circle transference remains an explicit independent compound hypothesis. The classical primitive sum-of-two-squares criterion is an additional explicit independent arithmetic hypothesis for Section9 reductions; it contains no own-paper conclusion and is not declared as a Lean axiom.

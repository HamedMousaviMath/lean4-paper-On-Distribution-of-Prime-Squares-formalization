# Checkpoint 998: Actual Orlicz almost-everywhere and L1 convergence with the same limit

Lean completes the own Orlicz pointwise and L1 convergence deduction for the actual ergodic averages. It applies the exact bounded-class independent input to every checked truncation, proves L1 Cauchy convergence on the bounded class by dominated convergence, extends through the actual uniformly bounded L1 operators and truncation density, and obtains a genuine L1 limit. A convergent subsequence in measure and the proved almost-everywhere Cauchy property identify the full pointwise limit with that same L1 limit. Actual integrability of every average, vanishing L1 seminorm and vanishing integral norm of the difference are explicit. No unbounded Orlicz or L1 density-extension conclusion is an independent input. The remaining final step is common-constant/source assembly for Corollary7.46.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| OrliczErgodicConvergence.lean | 2 |

- `bounded_truncation_cauchy_from_input`
- `orlicz_ergodic_convergence`

<!-- checkpoint-verification -->

## Verification

All 1065 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4687-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 3054 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1067 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed source results under their paper hypotheses remain unchanged. Lemma 3.21, Theorems 1.1 and 1.3, Propositions 4.19 and 6.21, and every clause of Theorem 7.2 are complete checked implications under their separately recorded independent inputs. Theorem 7.2 covers all three actual square families, every integer cutoff N >= 2, arbitrary complex finite support, common constants, actual finite level sets and truncated, unrestricted modular and restricted estimates. The square-sign reflection is proved. The stronger standalone auxiliary ranges and later deductions retain their separately reviewed scopes. Theorem7.2 consumes the precise independent scalar quadratic Weyl approximation (including its unproved published-theorem selection/reduction/phase bridge), general Tao construction, IW multiplier, major-arc/Shannon sampling, continuous/interpolation, signed-sequence and smooth multifrequency inputs, Page uniqueness and compatible raw prime-distribution data. All own ordinary and prime circle approximations, quantitative high/low comparisons, restricted estimates, parameter optimization and final source assembly are proved. No such own-paper conclusion is an independent input. Earlier Theorems1.1/1.3 and Propositions4.19/6.21 retain their separate recorded inputs. The full-square global/local stopping hypotheses for the earlier theorems are not used by the new ordinary-square IW route. The ergodic route now records precise general strong/modular Calderon interfaces and a bounded-class polynomial pointwise interface, including its unproved published-theorem and PNT/Abel/prime-power normalization bridge. No unbounded Orlicz or source prime-enumeration endpoint is assumed; these remain deductions to prove.

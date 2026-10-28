# Checkpoint 987: Actual ergodic strong maximal bound with the source quantitative rate

Lean transfers the proved actual Corollary 7.6 to the actual ergodic maximal operators for all three families, with exactly the same exponential p dependence. One constant is chosen before the probability system, family, exponent and function. For every 1 < p ≤ 2 and every Lp input, the conclusion includes almost-everywhere finiteness of the proper extended maximum, actual Lp membership of its real representative and the stated norm bound. Only the explicit independent general strong Calderon theorem is newly consumed; no source-specific ergodic norm estimate is assumed. The modular and Orlicz convergence clauses remain subsequent deductions.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| ErgodicStrongMaximal.lean | 1 |

- `ergodic_strong_maximal_source`

<!-- checkpoint-verification -->

## Verification

All 1054 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4676-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 3020 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1056 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed source results under their paper hypotheses remain unchanged. Lemma 3.21, Theorems 1.1 and 1.3, Propositions 4.19 and 6.21, and every clause of Theorem 7.2 are complete checked implications under their separately recorded independent inputs. Theorem 7.2 covers all three actual square families, every integer cutoff N >= 2, arbitrary complex finite support, common constants, actual finite level sets and truncated, unrestricted modular and restricted estimates. The square-sign reflection is proved. The stronger standalone auxiliary ranges and later deductions retain their separately reviewed scopes. Theorem7.2 consumes the precise independent scalar quadratic Weyl approximation (including its unproved published-theorem selection/reduction/phase bridge), general Tao construction, IW multiplier, major-arc/Shannon sampling, continuous/interpolation, signed-sequence and smooth multifrequency inputs, Page uniqueness and compatible raw prime-distribution data. All own ordinary and prime circle approximations, quantitative high/low comparisons, restricted estimates, parameter optimization and final source assembly are proved. No such own-paper conclusion is an independent input. Earlier Theorems1.1/1.3 and Propositions4.19/6.21 retain their separate recorded inputs. The full-square global/local stopping hypotheses for the earlier theorems are not used by the new ordinary-square IW route. The ergodic route now records precise general strong/modular Calderon interfaces and a bounded-class polynomial pointwise interface, including its unproved published-theorem and PNT/Abel/prime-power normalization bridge. No unbounded Orlicz or source prime-enumeration endpoint is assumed; these remain deductions to prove.

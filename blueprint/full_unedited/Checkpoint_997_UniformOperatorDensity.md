# Checkpoint 997: Uniform continuous-operator density argument for full L1 convergence

Lean proves the general uniform-operator density argument in normed spaces: a uniformly bounded sequence of actual continuous linear operators is Cauchy on an input whenever it is Cauchy on a sequence of approximants converging to that input. It checks the full two-index Cauchy condition and quantitative approximation errors. Applied to the proved L1 ergodic operators and bounded truncations, this supplies the unbounded L1 convergence extension without assuming that conclusion as an independent theorem.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| UniformOperatorDensity.lean | 1 |

- `uniform_operator_dense_cauchy`

<!-- checkpoint-verification -->

## Verification

All 1064 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4686-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 3052 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1066 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed source results under their paper hypotheses remain unchanged. Lemma 3.21, Theorems 1.1 and 1.3, Propositions 4.19 and 6.21, and every clause of Theorem 7.2 are complete checked implications under their separately recorded independent inputs. Theorem 7.2 covers all three actual square families, every integer cutoff N >= 2, arbitrary complex finite support, common constants, actual finite level sets and truncated, unrestricted modular and restricted estimates. The square-sign reflection is proved. The stronger standalone auxiliary ranges and later deductions retain their separately reviewed scopes. Theorem7.2 consumes the precise independent scalar quadratic Weyl approximation (including its unproved published-theorem selection/reduction/phase bridge), general Tao construction, IW multiplier, major-arc/Shannon sampling, continuous/interpolation, signed-sequence and smooth multifrequency inputs, Page uniqueness and compatible raw prime-distribution data. All own ordinary and prime circle approximations, quantitative high/low comparisons, restricted estimates, parameter optimization and final source assembly are proved. No such own-paper conclusion is an independent input. Earlier Theorems1.1/1.3 and Propositions4.19/6.21 retain their separate recorded inputs. The full-square global/local stopping hypotheses for the earlier theorems are not used by the new ordinary-square IW route. The ergodic route now records precise general strong/modular Calderon interfaces and a bounded-class polynomial pointwise interface, including its unproved published-theorem and PNT/Abel/prime-power normalization bridge. No unbounded Orlicz or source prime-enumeration endpoint is assumed; these remain deductions to prove.

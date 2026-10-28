# Checkpoint 977: General power layer-cake identity for the strong maximal deduction

Lean proves the general positive-power layer-cake identity for an arbitrary measure space and an a.e. nonnegative measurable function, using the explicit primitive of p t^(p-1) for every p > 0. Both the primitive and the extended nonnegative integral identity are checked. This starts the actual operator deduction of Corollary 7.6 from the proved truncated modular estimate; no layer-cake or current-paper strong maximal conclusion is added as an independent input. The subsequent steps will evaluate the truncated power kernel, bound the actual maximum and extend finite inputs.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| PositivePowerLayerCake.lean | 2 |

- `positivePower_primitive`
- `nonneg_power_layerCake`

<!-- checkpoint-verification -->

## Verification

All 1044 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4666-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2994 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1046 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed source results under their paper hypotheses remain unchanged. Lemma 3.21, Theorems 1.1 and 1.3, Propositions 4.19 and 6.21, and every clause of Theorem 7.2 are complete checked implications under their separately recorded independent inputs. Theorem 7.2 covers all three actual square families, every integer cutoff N >= 2, arbitrary complex finite support, common constants, actual finite level sets and truncated, unrestricted modular and restricted estimates. The square-sign reflection is proved. The stronger standalone auxiliary ranges and strong lp/ergodic/sieve deductions remain separately unfinished. Theorem7.2 consumes the precise independent scalar quadratic Weyl approximation (including its unproved published-theorem selection/reduction/phase bridge), general Tao construction, IW multiplier, major-arc/Shannon sampling, continuous/interpolation, signed-sequence and smooth multifrequency inputs, Page uniqueness and compatible raw prime-distribution data. All own ordinary and prime circle approximations, quantitative high/low comparisons, restricted estimates, parameter optimization and final source assembly are proved. No such own-paper conclusion is an independent input. Earlier Theorems1.1/1.3 and Propositions4.19/6.21 retain their separate recorded inputs. The full-square global/local stopping hypotheses for the earlier theorems are not used by the new ordinary-square IW route.

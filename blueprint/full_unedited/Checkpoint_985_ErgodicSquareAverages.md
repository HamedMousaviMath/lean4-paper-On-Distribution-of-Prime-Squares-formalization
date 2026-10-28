# Checkpoint 985: Actual ergodic square averages and a proper extended countable maximum

Lean defines the actual ergodic positive averages for an invertible measurable transformation, using the exact integer action and all three source families. It proves the positive square-iterate specialization, measurability, linear difference identity and uniform bounded-function estimate. The countable ergodic maximum is defined in the extended nonnegative reals, with every average dominated unconditionally; finite real-valued norm claims will explicitly include an almost-everywhere finiteness certificate. This prevents an unbounded supremum from collapsing under a conditional real supremum convention.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| ErgodicSquareAverages.lean | 10 |

- `integerSystemIterate_measurable`
- `integerSystemIterate_square`
- `sectionSevenFamily_shift`
- `ergodicPositiveAverage_square`
- `ergodicPositiveAverage_measurable`
- `ergodicMaximalENorm_measurable`
- `ergodicPositiveAverage_sub`
- `ergodicPositiveAverage_norm_bound`
- `ergodicMaximalENorm_dominates`
- `ergodicMaximalENorm_bounded`

<!-- checkpoint-verification -->

## Verification

All 1052 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4674-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 3018 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1054 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed source results under their paper hypotheses remain unchanged. Lemma 3.21, Theorems 1.1 and 1.3, Propositions 4.19 and 6.21, and every clause of Theorem 7.2 are complete checked implications under their separately recorded independent inputs. Theorem 7.2 covers all three actual square families, every integer cutoff N >= 2, arbitrary complex finite support, common constants, actual finite level sets and truncated, unrestricted modular and restricted estimates. The square-sign reflection is proved. The stronger standalone auxiliary ranges and later deductions retain their separately reviewed scopes. Theorem7.2 consumes the precise independent scalar quadratic Weyl approximation (including its unproved published-theorem selection/reduction/phase bridge), general Tao construction, IW multiplier, major-arc/Shannon sampling, continuous/interpolation, signed-sequence and smooth multifrequency inputs, Page uniqueness and compatible raw prime-distribution data. All own ordinary and prime circle approximations, quantitative high/low comparisons, restricted estimates, parameter optimization and final source assembly are proved. No such own-paper conclusion is an independent input. Earlier Theorems1.1/1.3 and Propositions4.19/6.21 retain their separate recorded inputs. The full-square global/local stopping hypotheses for the earlier theorems are not used by the new ordinary-square IW route.

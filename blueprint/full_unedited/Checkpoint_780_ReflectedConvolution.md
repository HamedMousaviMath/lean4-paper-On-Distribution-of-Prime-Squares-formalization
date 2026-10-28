# Checkpoint 780: Reflection preserves convolution pairings and all decomposition constants

For an arbitrary complex kernel K, reflection K^R(z)=K(-z) satisfies the exact finite convolution identity (K^R*f)(x)=(K*(Rf))(-x) when the finite input set is also reflected. The module proves the corresponding finite complex and indicator pairings, with both input and output sets reflected and their cardinalities preserved by checkpoint779. It constructs R T R for continuous linear operators between any lp and lq with p,q>=1, including infinity, and proves exact equality of their operator norms. The actual OperatorHighLowBound, OperatorOrliczBound and KernelL2Bound predicates are each equivalent for K and K^R with every numerical parameter and constant unchanged. The low/high/error maps need not be linear; their norm bounds transfer through the involutive isometry. No analytic input is used for these results. This closes the general convolution-estimate part of the requested sign transfer; the next checkpoint identifies the literal plus-square formulas and support windows.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| ReflectedConvolution.lean | 19 |

- `reflectLpMap_apply`
- `reflectLpMap_involutive`
- `reflectLpMap_norm`
- `reflectLpMap_bound_iff`
- `reflectContinuousLinearMap_apply`
- `reflectContinuousLinearMap_eq`
- `reflectContinuousLinearMap_involutive`
- `reflectContinuousLinearMap_norm_le`
- `reflectContinuousLinearMap_norm`
- `finiteConvolution_reflect`
- `indicatorConvolution_reflect`
- `finiteKernelPairing_reflect`
- `restrictedKernelPairing_reflect`
- `operatorHighLowBound_reflect`
- `operatorHighLowBound_reflect_iff`
- `operatorOrliczBound_reflect`
- `operatorOrliczBound_reflect_iff`
- `kernelL2Bound_reflect`
- `kernelL2Bound_reflect_iff`

<!-- checkpoint-verification -->

## Verification

All 847 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4454-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2155 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 849 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results under their paper hypotheses remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. In addition, Lemma 3.21 and BOTH conclusions of Theorem 1.1 are complete checked implications under their explicit independent deep inputs. The PNT limits are used in the sharp Gauss/high bound; an imported PNT bridge is not integrated. Both source clauses of Proposition 6.21 are also complete checked implications under their recorded independent inputs. The whole paper, Proposition 4.19 and the later headline applications remain unfinished. See docs/THEOREM_1_1_EXTERNAL_INPUTS.md. PNT limits, raw compatible progression/Ren/Ghosh data, and the independent square decomposition remain explicit hypotheses. The smooth multifrequency boundary is only for later maximal applications.

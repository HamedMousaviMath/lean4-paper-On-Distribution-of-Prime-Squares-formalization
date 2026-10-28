# Checkpoint 781: Full and annular plus-square formulas equal reflected minus-square averages

The plus-square operators and kernels are defined directly by finite sums, independently of reflection. Lean proves that their convolution kernel is the reflection of the existing minus-square kernel and their operator is R T_- R. The full weighted average is exactly N^-1 times the sum over 0<n<=N of w(n)f(x+n^2); the annular version retains the exact natural-index range N/2<n<=N. Both are equivalent by involutive conjugation to the existing x-n^2 operators, with equal operator norms. The proofs allow arbitrary real arithmetic weights; neither n nor w(n) is negated. They therefore apply unchanged to ordinary square weights and von-Mangoldt weights. The positive-translation kernel is supported in [-N^2,-1], and its local input window is [x,x+N^2]. Lean proves the interval reflection and the actual indicator-convolution localization on that window. This is an exact transfer after reflecting the geometry, not a claim that an asymmetric support interval or a particular dyadic grid stays fixed. No manuscript replacement is required. The external analytic square theorem is untouched.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| SquareAverageReflection.lean | 18 |

- `finiteSquareKernel_reflection`
- `finitePlusSquareOperator_apply`
- `finitePlusSquareOperator_reflection`
- `finitePlusSquareOperator_norm`
- `finitePlusSquareKernel_finiteInput`
- `weightedSquareAverageKernel_reflection`
- `annularWeightedSquareAverageKernel_reflection`
- `plusSquareAverage_apply`
- `annularPlusSquareAverage_apply`
- `plusSquareAverage_reflection`
- `annularPlusSquareAverage_reflection`
- `minusSquareAverage_from_plus`
- `annularMinusSquareAverage_from_plus`
- `plusSquareAverage_opNorm`
- `annularPlusSquareAverage_opNorm`
- `squareAverageWindow_reflection`
- `finitePlusSquareKernel_support_interval`
- `finitePlusSquareKernel_localization`

<!-- checkpoint-verification -->

## Verification

All 848 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4455-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2173 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 850 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results under their paper hypotheses remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. In addition, Lemma 3.21 and BOTH conclusions of Theorem 1.1 are complete checked implications under their explicit independent deep inputs. The PNT limits are used in the sharp Gauss/high bound; an imported PNT bridge is not integrated. Both source clauses of Proposition 6.21 are also complete checked implications under their recorded independent inputs. The whole paper, Proposition 4.19 and the later headline applications remain unfinished. See docs/THEOREM_1_1_EXTERNAL_INPUTS.md. PNT limits, raw compatible progression/Ren/Ghosh data, and the independent square decomposition remain explicit hypotheses. The smooth multifrequency boundary is only for later maximal applications.

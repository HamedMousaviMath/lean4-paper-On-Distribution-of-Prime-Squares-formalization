# Checkpoint 1110: Rough real Fourier symbols and full Lp realizations

Constructed arbitrary essentially bounded measurable real Fourier symbols, the actual bounded real-line L2 multipliers and their Fourier formulas without any continuity assumption. Proved exact scalar multiplication of symbols, operators and inverse Fourier kernels. Defined a full Lp Fourier realization as an actual bounded operator on the whole real Lp space agreeing with the given rough L2 multiplier on its genuine L2 intersection; this avoids mistaking an intersection norm for a full-domain operator. Its scalar-multiple realization is constructed with no deep input. These are foundations for the remaining broad IW clause, not an assertion of the deep theorem or a completion of the source proposition.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| AEBoundedRealMultipliers.lean | 8 |

- `aeRealProduct_memLp`
- `aeRealMultiplyValue_ae`
- `aeRealMultiplyValue_norm_le`
- `aeRealMultiply_ae`
- `realLineFourier_aeMultiplier`
- `aeRealLineMultiplier_norm_le`
- `aeRealLineMultiplier_smul`
- `aeRealSymbol_smul_inverse_kernel`

<!-- checkpoint-verification -->

## Verification

All 1177 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4968-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 3586 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1179 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The current complete manuscript upload confirms the independent admissibility coefficient. The full generic sparse recursion is proved under its normal local hypothesis. The unchanged upload and a separate selected copy with the previously approved factor-four application restored are preserved. Two earlier source statements remain partial: the original strong minor-arc clause and the broad standalone quantitative IW function classes. The full multifrequency lemma and denominator corollary, including measurable fixed symbols, are complete conditional implications. Section9 mapping is saved and its reductions are authorized; later circle-method and sieve conclusions remain internal proof obligations. The rational smooth multifrequency theorem with circle transference remains an explicit independent compound hypothesis. The classical primitive sum-of-two-squares criterion is an additional explicit independent arithmetic hypothesis for Section9 reductions; it contains no own-paper conclusion and is not declared as a Lean axiom.

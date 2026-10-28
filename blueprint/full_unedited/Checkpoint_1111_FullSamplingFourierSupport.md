# Checkpoint 1111: Full Lp Fourier support and bandlimited sampling classes

Implemented Fourier support on the whole real Lp space using Mathlib's actual tempered-distribution Fourier transform, including p=infinity. Implemented the integer Fourier-support condition by its literal Schwartz test series and proved absolute convergence for every integer lp input, so no totalized divergent series can satisfy the condition vacuously. Implemented actual finite cyclic Fourier components and the full bandlimited real/cyclic Lp class, with continuous representatives retained for point sampling. Proved support enlargement and the equality between the full fibre-Lp norm and the previously normalized iterated real/cyclic norm. These classes do not impose Schwartz, integrability or L2 conditions. The general deep sampling theorems and source applications remain the next step.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| FullSamplingFourierSupport.lean | 5 |

- `realLpSpectrumIn_mono`
- `realLpSpectrumIn_interval_mono`
- `schwartz_integer_test_summable`
- `integerLpSpectrumIn_mono`
- `cyclicFunctionLp_size`

<!-- checkpoint-verification -->

## Verification

All 1178 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4969-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 3591 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1180 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The current complete manuscript upload confirms the independent admissibility coefficient. The full generic sparse recursion is proved under its normal local hypothesis. The unchanged upload and a separate selected copy with the previously approved factor-four application restored are preserved. Two earlier source statements remain partial: the original strong minor-arc clause and the broad standalone quantitative IW function classes. The full multifrequency lemma and denominator corollary, including measurable fixed symbols, are complete conditional implications. Section9 mapping is saved and its reductions are authorized; later circle-method and sieve conclusions remain internal proof obligations. The rational smooth multifrequency theorem with circle transference remains an explicit independent compound hypothesis. The classical primitive sum-of-two-squares criterion is an additional explicit independent arithmetic hypothesis for Section9 reductions; it contains no own-paper conclusion and is not declared as a Lean axiom.

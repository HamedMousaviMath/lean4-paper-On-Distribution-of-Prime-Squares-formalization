# Checkpoint 1112: Full rough-symbol adelic IW application and cyclic basis correction

Implemented the independent general full-domain adelic IW interface, with its rough-symbol limiting and finite-quotient/kernel bridges explicitly unproved. It quantifies over arbitrary good coprime data and arbitrary spatial cyclic families, not the source probability-measure specialization. Proved the exact rank-one kernel factorization and the full real-Q rough multiplier application. The output is an actual bounded operator on all integer lp inputs, with its literal finite-convolution Fourier kernel and operator norm <=C_rk times the actual full real Lp operator norm. The real/cyclic product estimate is discharged by the unconditional full-Lp module. Corrected the newly introduced sampling basis to denominators dividing P, with exact declared source hashes and required dependency rebuild; no source completion was awarded to the earlier incorrect class.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| FullAdelicIWApplication.lean | 4 |

- `adelicProjectedKernel_rank_one`
- `iwRoughKernel_finite_formula`
- `quantitative_real_iw_full_rough_multiplier`
- `source_iw_rough_multiplier_norm`

<!-- checkpoint-verification -->

## Verification

All 1179 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4970-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 3595 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1181 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The current complete manuscript upload confirms the independent admissibility coefficient. The full generic sparse recursion is proved under its normal local hypothesis. The unchanged upload and a separate selected copy with the previously approved factor-four application restored are preserved. Two earlier source statements remain partial: the original strong minor-arc clause and the broad standalone quantitative IW function classes. The full multifrequency lemma and denominator corollary, including measurable fixed symbols, are complete conditional implications. Section9 mapping is saved and its reductions are authorized; later circle-method and sieve conclusions remain internal proof obligations. The rational smooth multifrequency theorem with circle transference remains an explicit independent compound hypothesis. The classical primitive sum-of-two-squares criterion is an additional explicit independent arithmetic hypothesis for Section9 reductions; it contains no own-paper conclusion and is not declared as a Lean axiom.

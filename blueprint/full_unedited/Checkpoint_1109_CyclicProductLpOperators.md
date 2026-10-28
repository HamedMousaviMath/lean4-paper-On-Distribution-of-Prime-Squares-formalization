# Checkpoint 1109: Full real Lp cyclic product operator bound

Implemented the normalized cyclic Lp norm on families of actual Banach-space elements and proved its pointwise domination, translation and finite-sum properties. Proved the product operator bound for arbitrary full real Lp fibres, every finite exponent p>=1, arbitrary bounded real operator and every finite cyclic complex measure: the exact norm is at most its total variation times the real operator norm. The TV<=1 consequence has no Schwartz or L2-intersection restriction and adds no independent theorem hypothesis. This is the full-domain product estimate used in the broad IW multiplier application. The remaining deep IW and sampling theorems are still explicit external inputs, and the full proposition is not yet complete.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| CyclicProductLpOperators.lean | 5 |

- `cyclicFamilyLpSize_mono`
- `cyclicFamilyLpSize_translate`
- `cyclicFamilyLpSize_finsetSum`
- `cyclicRealOperator_Lp_bound`
- `cyclicRealOperator_TV_one_bound`

<!-- checkpoint-verification -->

## Verification

All 1176 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4967-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 3578 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1178 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The current complete manuscript upload confirms the independent admissibility coefficient. The full generic sparse recursion is proved under its normal local hypothesis. The unchanged upload and a separate selected copy with the previously approved factor-four application restored are preserved. Two earlier source statements remain partial: the original strong minor-arc clause and the broad standalone quantitative IW function classes. The full multifrequency lemma and denominator corollary, including measurable fixed symbols, are complete conditional implications. Section9 mapping is saved and its reductions are authorized; later circle-method and sieve conclusions remain internal proof obligations. The rational smooth multifrequency theorem with circle transference remains an explicit independent compound hypothesis. The classical primitive sum-of-two-squares criterion is an additional explicit independent arithmetic hypothesis for Section9 reductions; it contains no own-paper conclusion and is not declared as a Lean axiom.

# Checkpoint 1090: Disjoint measurable multiplier assembly independent of scale and cutoff

For a finite separated circle family, bounded measurable symbols supported in the respective disjoint cutoffs combine to one measurable symbol of essential supremum at most1. The exact localized operator composition is proved for arbitrary continuous outer symbols supported in those cutoffs. The merged symbol is fixed independently of the scale and of the denominator cutoff. This is an internal checked consequence of disjoint supports, with no further deep input.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| DisjointAEMultiplierAssembly.lean | 3 |

- `finiteAEMultiplier_sum_measurable`
- `disjointAEMultiplier_sum_bound`
- `disjointAEMultiplierSymbol_local_comp`

<!-- checkpoint-verification -->

## Verification

All 1157 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4948-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 3496 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1159 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The current complete manuscript upload confirms the independent admissibility coefficient. The full generic sparse recursion is proved under its normal local hypothesis. The unchanged upload and a separate selected copy with the previously approved factor-four application restored are preserved. Four substantive auxiliaries remain partial. Section9 mapping and reductions are now authorized; later analytic and sieve inputs remain explicit. The rational smooth multifrequency theorem together with circle transference is an explicit independent compound hypothesis; its existence is unproved. Its predicate contains no own-paper annular or truncated maximal conclusion. See docs/RATIONAL_MULTIFREQUENCY_BOUNDARY.md.

# Checkpoint 1089: Measurable bounded circle multipliers and exact localized composition

Constructed actual bounded L2 multiplier operators for arbitrary almost everywhere strongly measurable, essentially bounded circle symbols. The checked Fourier representation, norm bounds and localization/composition identity work on all integer L2 inputs. This removes the continuity restriction before proving the fixed bounded multiplier clause of the denominator corollary. No analytic theorem is assumed for this construction, and no paper claim is newly credited at this supporting stage.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| AEBoundedCircleMultipliers.lean | 11 |

- `aeCircleProduct_memLp`
- `aeCircleMultiplyValue_ae`
- `aeCircleMultiplyValue_norm_le`
- `aeCircleMultiply_ae`
- `aeCircleMultiply_norm_le`
- `aeCircleMultiply_opNorm_le`
- `aeIntegerMultiplier_apply`
- `integerFourier_aeMultiplier`
- `aeIntegerMultiplier_norm_le`
- `aeIntegerMultiplier_opNorm_le`
- `aeIntegerMultiplier_localized_comp`

<!-- checkpoint-verification -->

## Verification

All 1156 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4947-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 3493 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1158 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The current complete manuscript upload confirms the independent admissibility coefficient. The full generic sparse recursion is proved under its normal local hypothesis. The unchanged upload and a separate selected copy with the previously approved factor-four application restored are preserved. Four substantive auxiliaries remain partial. Section9 mapping and reductions are now authorized; later analytic and sieve inputs remain explicit. The rational smooth multifrequency theorem together with circle transference is an explicit independent compound hypothesis; its existence is unproved. Its predicate contains no own-paper annular or truncated maximal conclusion. See docs/RATIONAL_MULTIFREQUENCY_BOUNDARY.md.

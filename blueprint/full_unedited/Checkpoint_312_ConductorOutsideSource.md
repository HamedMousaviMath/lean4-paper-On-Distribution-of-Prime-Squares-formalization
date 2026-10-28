# Checkpoint 312: Exact disappearance of exceptional terms beyond the source cutoff

Exact disappearance of exceptional terms beyond the source cutoff. The extra Q*q0/B0<=R restriction is removed. For every positive conductor, the original source cutoff R is retained; only the working geometric radius is enlarged to R^2. If the conductor exceeds R, its actual source coefficients and exceptional denominator set vanish. Under Q>=2, Q<=R and 2R^8<=N^2, the original low symbol has its full finite-input local estimate and all-input l1-to-linfinity norm bound. The paper range R^4<=N/2 implies the new geometric budget. Sharp high/multifrequency estimates and Theorem 1.1 remain open.


## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| ConductorOutsideSource.lean | 5 |

- `centeredLowSymbol_coefficient_zero`
- `circleLowTerm_coefficient_zero`
- `sourceLowModel_conductor_outside`
- `realExceptionalDenominators_empty`
- `realExceptionalLowModel_empty`

<!-- checkpoint-verification -->

## Verification

All 379 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 3986-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 1447 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 381 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. Published Ren and Ghosh quadratic exponential-sum estimates, when consumed, remain displayed raw theorem hypotheses; the progression-prefix estimate also remains an explicit unproved input. No own-paper analytic conclusion is assumed.

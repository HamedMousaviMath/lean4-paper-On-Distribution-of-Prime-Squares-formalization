# Checkpoint 314: The source low kernel and operator bounds throughout the full conductor range

The source low kernel and operator bounds throughout the full conductor range. The extra Q*q0/B0<=R restriction is removed. For every positive conductor, the original source cutoff R is retained; only the working geometric radius is enlarged to R^2. If the conductor exceeds R, its actual source coefficients and exceptional denominator set vanish. Under Q>=2, Q<=R and 2R^8<=N^2, the original low symbol has its full finite-input local estimate and all-input l1-to-linfinity norm bound. The paper range R^4<=N/2 implies the new geometric budget. Sharp high/multifrequency estimates and Theorem 1.1 remain open.


## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| SourceLowFullRangeBounds.lean | 3 |

- `sourceFullLow_L1_norm`
- `sourceFullLow_local`
- `sourceFullLow_kernel_decay`

<!-- checkpoint-verification -->

## Verification

All 381 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 3988-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 1451 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 383 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. Published Ren and Ghosh quadratic exponential-sum estimates, when consumed, remain displayed raw theorem hypotheses; the progression-prefix estimate also remains an explicit unproved input. No own-paper analytic conclusion is assumed.

# Checkpoint 736: Actual prime-square three-piece decomposition and raw input boundary

Collects exact compatible raw progression/Ren/Ghosh data in an explicit external input structure, with no own-paper conclusions assumed. Combines the checked actual circle low operator, sharp high operator and actual error operator to prove the three-piece OperatorOrliczBound for the genuine annular von-Mangoldt square kernel, for all sufficiently large arithmetic scales. The complete dyadic cutoff range and the change from arithmetic N to spatial N^2 are checked. The existing Lean range is (min(c/7,1))/8; this stronger, correctly parenthesized range is retained. The uniform low constant, high constant with every c1>2, and error constant eight are proved. Theorem 1.1's endpoint and reconstruction remain open.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| PrimeSquareDistributionInputs.lean | 4 |

- `distribution_cutoff_constant_pos`
- `square_log_sqrt_le_double`
- `source_low_amplitude_orlicz`
- `primeSquare_orlicz_decomposition_large`

<!-- checkpoint-verification -->

## Verification

All 803 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4410-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 1982 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 805 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. See docs/THEOREM_1_1_EXTERNAL_INPUTS.md. PNT limits, raw compatible progression/Ren/Ghosh data, and the independent square decomposition remain explicit hypotheses. The smooth multifrequency boundary is only for later maximal applications.

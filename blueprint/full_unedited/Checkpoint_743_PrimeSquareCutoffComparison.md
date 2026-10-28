# Checkpoint 743: Positive full-average comparison and a dyadic upper cutoff

Proves positivity-based comparison of the genuine full von-Mangoldt kernel and restricted pairing at two arbitrary arithmetic cutoffs N<=M, retaining the exact M/N normalization. Also constructs a natural dyadic upper cutoff between N and 2N. These elementary deductions connect the checked dyadic full-average endpoint to arbitrary positive N without new analytic assumptions.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| PrimeSquareCutoffComparison.lean | 3 |

- `mangoldtSquareKernel_cutoff_bound`
- `mangoldtSquarePairing_cutoff_bound`
- `exists_dyadic_upper_nat`

<!-- checkpoint-verification -->

## Verification

All 810 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4417-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2003 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 812 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. See docs/THEOREM_1_1_EXTERNAL_INPUTS.md. PNT limits, raw compatible progression/Ren/Ghosh data, and the independent square decomposition remain explicit hypotheses. The smooth multifrequency boundary is only for later maximal applications.

# Checkpoint 735: Independent square input and checked full-to-annular transfer

Introduces a precise, explicitly unproved external interface for the independent full unweighted-square decomposition. Its global norm form is a compound consequence of Han–Lacey–Yang's published Fourier construction and local estimate, including reflection; it is not claimed to have been imported from Mathlib. Proves the actual full-to-annular identity on finite indicators and deduces the annular high/low operator bounds at even cutoffs, with the spatial-scale and one-half factors checked in Lean. No prime-square conclusion is an assumption of this interface. Theorem 1.1 remains open pending assembly.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| IndependentSquareDecomposition.lean | 2 |

- `annular_indicator_two_mul`
- `fullSquare_decomposition_annular_two_mul`

<!-- checkpoint-verification -->

## Verification

All 802 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4409-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 1978 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 804 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. See docs/THEOREM_1_1_EXTERNAL_INPUTS.md. The PNT limits, raw compatible progression/Ren/Ghosh estimates, and independent unweighted-square decomposition remain explicit hypotheses. The smooth multifrequency hypothesis is confined to the separate maximal development.

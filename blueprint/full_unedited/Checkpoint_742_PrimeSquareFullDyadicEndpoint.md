# Checkpoint 742: Sharp full-average endpoint at every dyadic cutoff

Proves the sharp restricted endpoint for the genuine FULL von-Mangoldt square average at every dyadic arithmetic cutoff. The proof uses the exact descending-annulus pairing identity, extends each annular bound to density above one with the actual Chebyshev l2 estimate, preserves the paper Phi by density monotonicity, and sums the resulting one-third-power geometric weights. Every rescaling factor and the uniform geometric constant are checked in Lean. This completes the full dyadic endpoint, conditional on the already recorded independent deep inputs; arbitrary arithmetic cutoffs, interval normalization and strong interpolation remain.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| PrimeSquareFullDyadicEndpoint.lean | 4 |

- `finiteSetDensity_scale_antitone`
- `primeSquare_annular_comparison`
- `dyadic_descending_ratio`
- `primeSquare_full_endpoint_dyadic`

<!-- checkpoint-verification -->

## Verification

All 809 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4416-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2000 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 811 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. See docs/THEOREM_1_1_EXTERNAL_INPUTS.md. PNT limits, raw compatible progression/Ren/Ghosh data, and the independent square decomposition remain explicit hypotheses. The smooth multifrequency boundary is only for later maximal applications.

# Checkpoint 744: Sharp full-average endpoint for every positive arithmetic cutoff

Proves the sharp restricted endpoint for the actual full von-Mangoldt square average at EVERY positive integer cutoff N, uniformly over all finite sets with density at most one. The proof chooses an actual dyadic upper cutoff in [N,2N], uses the checked positivity comparison, bounds the density change by sixteen, and applies the checked fixed-factor comparison for the exact Phi. The outside constant changes, while every requested coefficient cstar>4*sqrt(3)/9 is preserved. The exact source interval normalization and strong conclusion are the remaining assembly steps.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| PrimeSquareFullEndpoint.lean | 2 |

- `square_density_bounded_ratio`
- `primeSquare_full_endpoint`

<!-- checkpoint-verification -->

## Verification

All 811 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4418-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2005 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 813 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. See docs/THEOREM_1_1_EXTERNAL_INPUTS.md. PNT limits, raw compatible progression/Ren/Ghosh data, and the independent square decomposition remain explicit hypotheses. The smooth multifrequency boundary is only for later maximal applications.

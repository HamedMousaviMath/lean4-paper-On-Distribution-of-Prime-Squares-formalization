# Checkpoint 741: Exact full-average pairing and endpoint rescaling

Proves exact reconstruction of the genuine full von-Mangoldt kernel pairing from descending dyadic annuli, using the already checked identity of actual continuous operators. Proves the exact change of finite-set density between two square spatial scales and the two-thirds endpoint scaling identity, including all normalization factors. These are equalities, not numerical checks or new analytic assumptions, and are used in summing the annular endpoint to the full average.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| DyadicEndpointReconstruction.lean | 3 |

- `mangoldtPairing_dyadic_reconstruction`
- `square_density_ratio`
- `square_endpoint_rescale`

<!-- checkpoint-verification -->

## Verification

All 808 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4415-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 1996 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 810 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. See docs/THEOREM_1_1_EXTERNAL_INPUTS.md. PNT limits, raw compatible progression/Ren/Ghosh data, and the independent square decomposition remain explicit hypotheses. The smooth multifrequency boundary is only for later maximal applications.

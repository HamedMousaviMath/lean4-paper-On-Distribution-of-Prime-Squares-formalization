# Checkpoint 745: Theorem 1.1 restricted endpoint with the exact source interval

Proves the exact source interval I=[-N^2,2N^2] intersect Z has cardinality 3N^2+1, and checks its comparison with the spatial scale N^2. Exports theorem_1_1_restricted: the FIRST conclusion of Theorem 1.1 for the genuine full von-Mangoldt average, every positive N, all F,G contained in the exact interval, and every coefficient cstar>4*sqrt(3)/9. The proof also handles source densities whose N^2-normalized version exceeds one, using the actual l2 estimate. Constants and both normalizations are checked. The strong conclusion is still being assembled; Theorem 1.1 is not yet marked fully complete.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| PrimeSquareSourceInterval.lean | 5 |

- `primeSquareSourceInterval_card`
- `primeSquareSourceInterval_card_bounds`
- `finiteSetDensity_scale_ratio`
- `primeSquare_full_comparison`
- `theorem_1_1_restricted`

<!-- checkpoint-verification -->

## Verification

All 812 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4419-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2010 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 814 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. See docs/THEOREM_1_1_EXTERNAL_INPUTS.md. PNT limits, raw compatible progression/Ren/Ghosh data, and the independent square decomposition remain explicit hypotheses. The smooth multifrequency boundary is only for later maximal applications.

# Checkpoint 739: All dyadic annular scales and monotonicity of the exact Orlicz loss

Combines the checked large-scale annular endpoint with the elementary finite-scale bound to prove the sharp endpoint for every dyadic arithmetic cutoff, uniformly over finite input and test sets with density at most one. Also proves monotonicity of sqrt(L)/(2+log L) for L>=2 and the corresponding density monotonicity of the exact paper Phi. These facts allow summation over annuli without changing the endpoint coefficient. The two final Theorem 1.1 conclusions still require the full-average and arbitrary-cutoff transfers and strong interpolation.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| PrimeSquareDyadicAnnularEndpoint.lean | 3 |

- `orliczWeight_half_mono`
- `paperPhi_half_antitone`
- `primeSquare_annular_endpoint_dyadic`

<!-- checkpoint-verification -->

## Verification

All 806 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4413-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 1991 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 808 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. See docs/THEOREM_1_1_EXTERNAL_INPUTS.md. PNT limits, raw compatible progression/Ren/Ghosh data, and the independent square decomposition remain explicit hypotheses. The smooth multifrequency boundary is only for later maximal applications.

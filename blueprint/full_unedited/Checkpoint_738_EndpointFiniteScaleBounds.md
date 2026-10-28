# Checkpoint 738: Elementary completion of the finite arithmetic scales

Proves a uniform elementary point bound for the actual annular von-Mangoldt square kernel, using injectivity of natural-number squares and Lambda(n)<=log N<=N. Deduces a finite-scale restricted endpoint bound with an explicit T^2 constant and the exact paper Phi. This handles all arithmetic scales below a fixed threshold, including empty input sets, without placing a finite-scale decomposition among the external assumptions. The large-scale sharp endpoint was checked separately; the full-average reconstruction remains to be assembled.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| EndpointFiniteScaleBounds.lean | 3 |

- `mangoldtSquareKernel_point_bound`
- `restricted_pairing_card_bound`
- `annular_endpoint_finite_scale`

<!-- checkpoint-verification -->

## Verification

All 805 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4412-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 1988 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 807 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. See docs/THEOREM_1_1_EXTERNAL_INPUTS.md. PNT limits, raw compatible progression/Ren/Ghosh data, and the independent square decomposition remain explicit hypotheses. The smooth multifrequency boundary is only for later maximal applications.

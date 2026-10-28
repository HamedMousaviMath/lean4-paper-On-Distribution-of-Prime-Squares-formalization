# Checkpoint 740: Exact Orlicz loss under bounded changes of density

Proves the bounded-additive-shift estimate for the exact square-root Orlicz weight and the resulting multiplicative comparison for Phi when two densities differ by at most a fixed factor. The endpoint coefficient is preserved exactly; the fixed factor only changes the outside constant. This is needed for the dyadic-to-arbitrary arithmetic cutoff and source interval normalization in Theorem 1.1. No new analytic input is used.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| OrliczScaleComparison.lean | 2 |

- `orliczWeight_half_add_le`
- `paperPhi_half_fixed_rescale`

<!-- checkpoint-verification -->

## Verification

All 807 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4414-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 1993 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 809 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. See docs/THEOREM_1_1_EXTERNAL_INPUTS.md. PNT limits, raw compatible progression/Ren/Ghosh data, and the independent square decomposition remain explicit hypotheses. The smooth multifrequency boundary is only for later maximal applications.

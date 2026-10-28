# Checkpoint 746: Strong prime-square improving by checked interpolation

Proves a uniform restricted power estimate for every 3/2<q<=2 by absorbing the checked endpoint Phi into an arbitrarily small density power. Uses the actual l2 bound to cover all finite sets and instantiates the checked strong interpolation theorem. The result is a genuine lp-to-lq continuous kernel realization with the sharp spatial scaling, for the entire range 3/2<p<=2; the p=2 case is handled by the actual Chebyshev l2 operator. No strong estimate is assumed as an external input. Identification with the literal finite weighted average and final source normalization follow next.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| PrimeSquareStrongImproving.lean | 3 |

- `primeSquare_fixed_coefficient`
- `primeSquare_restricted_power_uniform`
- `primeSquare_strong_kernel_uniform`

<!-- checkpoint-verification -->

## Verification

All 813 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4420-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2013 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 815 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. See docs/THEOREM_1_1_EXTERNAL_INPUTS.md. PNT limits, raw compatible progression/Ren/Ghosh data, and the independent square decomposition remain explicit hypotheses. The smooth multifrequency boundary is only for later maximal applications.

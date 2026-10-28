# Checkpoint 143: Vanishing of the genuine countable maximal tails

The l2 norm of the true countable maximal tail tends to zero as the starting exponent tends to infinity for every norm-summable operator family and every l2 input. The proof bounds it by the tail sum of the operator norms times norm(f), and uses the proved vanishing of absolutely convergent series tails.

Lean also proves convergence of the maximal-tail vectors themselves to zero in real l2. The positive envelope and true supremum are not conflated, and no finite-scale limit is left unproved.

This gives a rigorous continuation property for the actual error family once its norm summability is supplied. It does not assert convergence of the remaining main model or prove an ergodic endpoint theorem.


## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| MaximalTailVanishing.lean | 2 |

- `operatorMaximalL2_tail_norm_tendsto_zero`
- `operatorMaximalL2_tail_tendsto_zero`

<!-- checkpoint-verification -->

## Verification

All 210 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 3735-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 1095 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 212 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. Published Ren and Ghosh quadratic exponential-sum estimates, when consumed, remain displayed raw theorem hypotheses; the progression-prefix estimate also remains an explicit unproved input. No own-paper analytic conclusion is assumed.

# Checkpoint 135: An all-input countable maximal l2 bound

The l2 norm of the genuine countable maximal function is bounded by the norm of the countable positive envelope. Consequently,

    norm(sup_j |T_j f|)_2 <= (sum_j norm(T_j))*norm(f)_2.

Lean proves the pointwise nonnegativity and norm comparisons required for the l2 monotonicity argument. This is a complete countable all-input estimate under operator-norm summability, not merely an inequality for finite scale collections.

Applied to the proved dyadic error decay, it will provide the maximal error term without assuming a new multifrequency theorem. It does not bound the separate high or low operators.


## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| OperatorMaximalNorm.lean | 2 |

- `operatorMaximalL2_norm_le_envelope`
- `operatorMaximalL2_norm_bound`

<!-- checkpoint-verification -->

## Verification

All 202 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 3727-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 1077 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 204 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. Published Ren and Ghosh quadratic exponential-sum estimates, when consumed, remain displayed raw theorem hypotheses; the progression-prefix estimate also remains an explicit unproved input. No own-paper analytic conclusion is assumed.

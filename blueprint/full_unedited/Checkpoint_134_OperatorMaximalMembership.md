# Checkpoint 134: A concrete l2 realization of the countable maximal function

The actual countable maximal value is proved to belong to real l2 by pointwise domination by the constructed l2 envelope. A concrete l2 realization operatorMaximalL2 is defined, and its value at every integer is exactly sup_j norm(T_j f(x)).

The proof applies to every complex l2 input. The function is not a finite maximum, an unspecified dominating function or an almost-everywhere representative of an unproved supremum. Boundedness of the value set and norm summability have already been established.


## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| OperatorMaximalMembership.lean | 2 |

- `operatorMaximalValue_memLp`
- `operatorMaximalL2_apply`

<!-- checkpoint-verification -->

## Verification

All 201 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 3726-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 1075 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 203 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. Published Ren and Ghosh quadratic exponential-sum estimates, when consumed, remain displayed raw theorem hypotheses; the progression-prefix estimate also remains an explicit unproved input. No own-paper analytic conclusion is assumed.

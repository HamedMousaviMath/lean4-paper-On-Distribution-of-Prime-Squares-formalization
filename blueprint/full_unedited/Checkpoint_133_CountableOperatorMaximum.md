# Checkpoint 133: A bounded true countable maximal function

The actual pointwise countable supremum sup_j norm(T_j f(x)) is defined as operatorMaximalValue. Lean proves the set of values is bounded above by the countable envelope before using conditional supremum inequalities over the real numbers.

The supremum dominates every operator output, is nonnegative, and is at most the countable envelope. This rules out interpreting an unbounded real supremum through a default total definition. All statements require and use summability of the operator norms to supply a genuine bound.

The next step proves that this actual maximal function, rather than just its majorant, belongs to l2.


## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| CountableOperatorMaximum.lean | 4 |

- `operatorNormValues_bddAbove`
- `operatorMaximalValue_dominates`
- `operatorMaximalValue_nonneg`
- `operatorMaximalValue_le_envelope`

<!-- checkpoint-verification -->

## Verification

All 200 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 3725-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 1073 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 202 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. Published Ren and Ghosh quadratic exponential-sum estimates, when consumed, remain displayed raw theorem hypotheses; the progression-prefix estimate also remains an explicit unproved input. No own-paper analytic conclusion is assumed.

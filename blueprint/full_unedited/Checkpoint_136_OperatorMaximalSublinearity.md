# Checkpoint 136: Sublinearity of the actual countable maximal function

The true countable maximal function is proved subadditive on l2 inputs and invariant under replacing f by -f. A scalar bound operatorMaximalValue(z*f)<=|z|*operatorMaximalValue(f) is also proved for every complex scalar z.

The proofs use the linearity of the actual operators, the triangle inequality and the previously established boundedness of the real supremum. They do not assume that taking a countable supremum preserves linearity. These properties will give the final Lipschitz estimate for the maximal-error map.


## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| OperatorMaximalSublinearity.lean | 3 |

- `operatorMaximalValue_add`
- `operatorMaximalValue_neg`
- `operatorMaximalValue_smul_le`

<!-- checkpoint-verification -->

## Verification

All 203 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 3728-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 1080 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 205 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. Published Ren and Ghosh quadratic exponential-sum estimates, when consumed, remain displayed raw theorem hypotheses; the progression-prefix estimate also remains an explicit unproved input. No own-paper analytic conclusion is assumed.

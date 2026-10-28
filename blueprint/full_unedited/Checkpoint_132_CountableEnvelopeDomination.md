# Checkpoint 132: Pointwise domination by the countable envelope

The countable envelope is proved nonnegative at every integer and to dominate norm(T_j f(x)) for every index j. Every existing finite operator envelope is also bounded pointwise by the countable envelope.

The proofs use the exact coordinate series and its established summability. In particular, the finite-to-countable passage is justified for all l2 inputs rather than only for finitely supported functions. The bound contains all indices and has no dependence on the size of a finite truncation.

This is a functional-analytic consequence of norm summability, not a new deep analytic input.


## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| CountableEnvelopeDomination.lean | 3 |

- `countableOperatorEnvelope_nonneg`
- `countableOperatorEnvelope_dominates`
- `finiteOperatorEnvelope_le_countable`

<!-- checkpoint-verification -->

## Verification

All 199 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 3724-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 1069 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 201 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. Published Ren and Ghosh quadratic exponential-sum estimates, when consumed, remain displayed raw theorem hypotheses; the progression-prefix estimate also remains an explicit unproved input. No own-paper analytic conclusion is assumed.

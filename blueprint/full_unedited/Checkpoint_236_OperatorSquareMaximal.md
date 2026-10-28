# Checkpoint 236: The countable operator maximal principle from square energy

The countable operator maximal principle from square energy. This module proves the exact finite or infinite statement in its Lean declarations with no proof placeholder and no added mathematical axiom. The square-function construction requires summability of squared output norms, rather than the stronger sum-of-norms hypothesis used in the earlier envelope argument. The symbol criterion is a proved implication from explicit frequency square bounds; it is not a claim that the paper's complete high or multifrequency estimate has already been established. The source annular collar stages retain beta in [0,1], the exact rational-scale onset and all dyadic powers. Theorem 1.1 remains open.


## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| OperatorSquareMaximal.lean | 2 |

- `operatorSquareEnergy_finite_bound`
- `operatorSquareEnergy_countable_maximal`

<!-- checkpoint-verification -->

## Verification

All 303 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 3910-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 1295 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 305 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. Published Ren and Ghosh quadratic exponential-sum estimates, when consumed, remain displayed raw theorem hypotheses; the progression-prefix estimate also remains an explicit unproved input. No own-paper analytic conclusion is assumed.

# Checkpoint 138: Monotonicity of the true countable maximal tails

Every tail of a norm-summable operator family is norm summable. Lean proves that moving the starting exponent from J to K>=J decreases the actual pointwise countable maximal function and its l2 norm.

The proof reindexes K+j exactly as J+(K-J+j); it does not discard indices informally or identify different scale-dependent data. The nonnegative real l2 realizations are compared using the pointwise inequalities already proved for the true supremum.

This supports quantitative approximation and continuity statements for dyadic error tails.


## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| MaximalTailMonotonicity.lean | 3 |

- `operator_tail_norm_summable`
- `operatorMaximalValue_tail_mono`
- `operatorMaximalL2_tail_mono`

<!-- checkpoint-verification -->

## Verification

All 205 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 3730-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 1085 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 207 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. Published Ren and Ghosh quadratic exponential-sum estimates, when consumed, remain displayed raw theorem hypotheses; the progression-prefix estimate also remains an explicit unproved input. No own-paper analytic conclusion is assumed.

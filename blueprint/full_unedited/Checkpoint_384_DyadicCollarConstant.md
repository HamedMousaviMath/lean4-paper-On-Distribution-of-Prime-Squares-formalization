# Checkpoint 384: Exact normalization of the denominator-block collar constant

The proved collar constant 96 C (2^s)^(-delta) 2^(s+1)/(pi Q) equals (192 C/(pi Q))(2^(1-delta))^s. All real power and natural power identities are retained exactly.


## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| DyadicCollarConstant.lean | 1 |

- `dyadic_collar_constant_identity`

<!-- checkpoint-verification -->

## Verification

All 451 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4058-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 1560 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 453 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. Published Ren and Ghosh quadratic exponential-sum estimates, when consumed, remain displayed raw theorem hypotheses; the progression-prefix estimate also remains an explicit unproved input. No own-paper analytic conclusion is assumed.

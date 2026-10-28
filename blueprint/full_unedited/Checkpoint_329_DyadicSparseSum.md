# Checkpoint 329: A proved sparse sum bound with exact zero support

A proved sparse sum bound with exact zero support. Rational separation gives at most one active center on every denominator block s>=2, while the two smallest scales retain all four possible small-denominator centers. The finite sums are partitioned exactly, including the denominator-one center and empty sets. The extra positive denominator exponent yields a genuinely summable geometric bound instead of a logarithm of the global cutoff.


## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| DyadicSparseSum.lean | 2 |

- `rational_sum_eq_active`
- `dyadic_sparse_sum_bound`

<!-- checkpoint-verification -->

## Verification

All 396 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4003-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 1481 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 398 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. Published Ren and Ghosh quadratic exponential-sum estimates, when consumed, remain displayed raw theorem hypotheses; the progression-prefix estimate also remains an explicit unproved input. No own-paper analytic conclusion is assumed.

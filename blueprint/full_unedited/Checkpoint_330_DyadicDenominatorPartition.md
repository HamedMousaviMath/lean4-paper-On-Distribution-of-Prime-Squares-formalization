# Checkpoint 330: Exact partition of all source rational centers by dyadic denominator

Exact partition of all source rational centers by dyadic denominator. Rational separation gives at most one active center on every denominator block s>=2, while the two smallest scales retain all four possible small-denominator centers. The finite sums are partitioned exactly, including the denominator-one center and empty sets. The extra positive denominator exponent yields a genuinely summable geometric bound instead of a logarithm of the global cutoff.


## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| DyadicDenominatorPartition.lean | 1 |

- `rational_dyadic_partition`

<!-- checkpoint-verification -->

## Verification

All 397 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4004-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 1482 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 399 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. Published Ren and Ghosh quadratic exponential-sum estimates, when consumed, remain displayed raw theorem hypotheses; the progression-prefix estimate also remains an explicit unproved input. No own-paper analytic conclusion is assumed.

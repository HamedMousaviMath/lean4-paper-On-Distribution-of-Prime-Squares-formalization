# Checkpoint 1097: Exact two-large-prime factorization with a primitive-compatible remaining factor

Proved the complete integer factorization underlying the truncated sieve. For m congruent1 modulo4 with m<z^4, if a prime3 modulo4 divides m and every such prime is at least z, then m=u*p1*p2 with positive u, ordered primes z<=p2<=p1, and every prime divisor of u congruent1 modulo4. Prime factor lists retain multiplicity, so p1=p2 is included. Positivity, exact products, ordering and all remaining prime divisors are proved. This is an unconditional arithmetic theorem with no primitive two-square, sieve or current-paper analytic hypothesis.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachTwoLargePrimeFactors.lean | 2 |

- `primeFactorsList_odd_mod_four`
- `primitive_obstruction_two_large_primes`

<!-- checkpoint-verification -->

## Verification

All 1164 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4955-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 3532 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1166 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The current complete manuscript upload confirms the independent admissibility coefficient. The full generic sparse recursion is proved under its normal local hypothesis. The unchanged upload and a separate selected copy with the previously approved factor-four application restored are preserved. Two source statements remain partial: the original strong minor-arc clause and the broad standalone quantitative IW function classes. The full multifrequency lemma and denominator corollary, including measurable fixed symbols, are complete conditional implications. Section9 mapping is saved and its reductions are authorized; later circle-method and sieve conclusions remain internal proof obligations. The rational smooth multifrequency theorem with circle transference remains an explicit independent compound hypothesis. The classical primitive sum-of-two-squares criterion is an additional explicit independent arithmetic hypothesis for Section9 reductions; it contains no own-paper conclusion and is not declared as a Lean axiom.

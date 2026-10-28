# Checkpoint 99: An unconditional uniform subpower bound for the divisor count

The exact divisor count is expressed as the product of exponent-plus-one factors over the distinct prime divisors of q. Using the uniform prime-power estimate of checkpoint 98, Lean bounds this product by A^omega(q)*q^epsilon. The product of prime powers is exactly q, with natural-to-real casts and real-power multiplication justified.

The existing elementary absorption of a fixed A^omega(q) into a small positive power of q then proves: for every fixed epsilon>0, there is C>0 such that tau(q)<=C*q^epsilon for every positive integer q. The constant is independent of q, includes q=1, and is selected before the denominator. The proof uses only unique factorization, finite products and proved asymptotic limits; it assumes no divisor bound, PNT or analytic number-theory theorem.

This is a supporting arithmetic estimate needed for Ren's prefactor. It does not assert a bound for a prime exponential sum without its explicit deep-input hypothesis, or close the full minor-arc or headline theorem gaps.


## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| DivisorProductGrowth.lean | 3 |

- `divisors_card_primePower_product`
- `divisors_card_weighted_power`
- `divisors_card_le_rpow`

<!-- checkpoint-verification -->

## Verification

All 166 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 3685-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 979 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 168 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. Published Ren and Ghosh quadratic exponential-sum estimates, when consumed, remain displayed raw theorem hypotheses; the progression-prefix estimate also remains an explicit unproved input. No own-paper analytic conclusion is assumed.

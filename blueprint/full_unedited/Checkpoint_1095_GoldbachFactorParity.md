# Checkpoint 1095: Multiplicity-sensitive modulo4 parity and the exactly-two factor count

Proved the exact modulo4 parity formula for lists whose factors are1 or3 modulo4, with bad factors retained with multiplicity. A product1 modulo4 has an even number of bad entries. The product lower bound shows that fewer than four entries can be at least z when the whole product is below z^4. If a bad factor exists, the bad list therefore has length exactly2, including repeated equal primes. These are unconditional arithmetic prerequisites for the actual Section9 truncation; no classical two-square criterion or Goldbach conclusion is assumed.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachFactorParity.lean | 7 |

- `mem_badModFourFactors`
- `mem_goodModFourFactors`
- `modFourFactors_product`
- `odd_list_product_mod_four`
- `modFourFactors_bad_count_even`
- `list_product_ge_length_power`
- `exactly_two_badModFourFactors`

<!-- checkpoint-verification -->

## Verification

All 1162 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4953-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 3526 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1164 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The current complete manuscript upload confirms the independent admissibility coefficient. The full generic sparse recursion is proved under its normal local hypothesis. The unchanged upload and a separate selected copy with the previously approved factor-four application restored are preserved. Two source statements remain partial: the original strong minor-arc clause and the broad standalone quantitative IW function classes. The full multifrequency lemma and denominator corollary, including measurable fixed symbols, are complete conditional implications. Section9 mapping is saved and its reductions are authorized; later circle-method and sieve conclusions remain internal proof obligations. The rational smooth multifrequency theorem together with circle transference is an explicit independent compound hypothesis; its existence is unproved. Its predicate contains no own-paper annular or truncated maximal conclusion. See docs/RATIONAL_MULTIFREQUENCY_BOUNDARY.md.

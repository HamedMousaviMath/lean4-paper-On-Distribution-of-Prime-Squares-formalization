# Checkpoint 1098: Actual truncated bad set and both directions of the sieve classification

Defined the actual truncated bad representation set with ordered prime factors, the closed lower cutoff and all remaining factor conditions. Proved that every sifted nonprimitive representation outside the explicit prime-divisor envelope belongs to this set, using the exact multiplicity-sensitive factorization. Proved both converse inclusions: every truncated bad representation is sifted and is not primitive, while every good representation in the source n residue class is sifted. The only unformalized arithmetic input is the already explicit independent primitive two-square criterion. No circle-method or sieve asymptotic input is used.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachTruncationSets.lean | 5 |

- `prime_three_mod_four_dvd_half`
- `goldbach_sifted_bad_factorization`
- `goldbachTruncatedBad_subset_sifted`
- `goldbachTruncatedBad_not_good`
- `goldbach_good_subset_sifted`

<!-- checkpoint-verification -->

## Verification

All 1165 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4956-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 3537 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1167 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The current complete manuscript upload confirms the independent admissibility coefficient. The full generic sparse recursion is proved under its normal local hypothesis. The unchanged upload and a separate selected copy with the previously approved factor-four application restored are preserved. Two source statements remain partial: the original strong minor-arc clause and the broad standalone quantitative IW function classes. The full multifrequency lemma and denominator corollary, including measurable fixed symbols, are complete conditional implications. Section9 mapping is saved and its reductions are authorized; later circle-method and sieve conclusions remain internal proof obligations. The rational smooth multifrequency theorem with circle transference remains an explicit independent compound hypothesis. The classical primitive sum-of-two-squares criterion is an additional explicit independent arithmetic hypothesis for Section9 reductions; it contains no own-paper conclusion and is not declared as a Lean axiom.

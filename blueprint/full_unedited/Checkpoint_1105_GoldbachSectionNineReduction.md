# Checkpoint 1105: Complete finite final-count reduction including the small-integer contribution

Completed the small-integer contribution and the actual all-admissible-n exceptional-set reduction, with explicit finite ceiling bounds. The source exponent choice K=A+2C+10 is used literally, producing the N^2*(log N)^(-A) bound from the unresolved internal lower/upper sieve, positive-gap and mean-square statements. Proved also that the positive-u closed L definition is exactly the source prime-divisor formulation: u=0 is excluded by the prime3 condition, so no additional restriction is hidden. This is a completed reduction, not a completed Goldbach headline theorem; internal analytic estimates remain unproved and are not new external hypotheses.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachSectionNineReduction.lean | 7 |

- `one_mod_four_prime_divisors_pos`
- `goldbachClosedL_source_form`
- `goldbachSmallNumbers_card_le_ceil`
- `goldbachLargeNumbers_range`
- `goldbach_exceptional_split`
- `goldbach_full_exceptional_count`
- `goldbach_section9_count_reduction`

<!-- checkpoint-verification -->

## Verification

All 1172 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4963-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 3563 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1174 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The current complete manuscript upload confirms the independent admissibility coefficient. The full generic sparse recursion is proved under its normal local hypothesis. The unchanged upload and a separate selected copy with the previously approved factor-four application restored are preserved. Two earlier source statements remain partial: the original strong minor-arc clause and the broad standalone quantitative IW function classes. The full multifrequency lemma and denominator corollary, including measurable fixed symbols, are complete conditional implications. Section9 mapping is saved and its reductions are authorized; later circle-method and sieve conclusions remain internal proof obligations. The rational smooth multifrequency theorem with circle transference remains an explicit independent compound hypothesis. The classical primitive sum-of-two-squares criterion is an additional explicit independent arithmetic hypothesis for Section9 reductions; it contains no own-paper conclusion and is not declared as a Lean axiom.

# Checkpoint 303: Exact exceptional cutoff filtering in the unit sum

Exact exceptional cutoff filtering in the unit sum. The original rational-indexed source circle symbol is identified with the ordinary denominator-unit model minus the optional induced exceptional model. Every denominator and conductor quotient is reindexed through proved bijections. Real Q and R, equality cutoff boundaries, the denominator-one term, all circle lifts and the exceptional negative sign are retained. Range conditions Q<=R, Q*q0/B0<=R and 2R^4<=N^2 are explicit; existence of analytic exceptional data is not assumed as a new axiom.


## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| ExceptionalUnitCutoffFilter.lean | 2 |

- `exceptionalUnitSum_filter`
- `exceptionalUnitSum_divisor_filter`

<!-- checkpoint-verification -->

## Verification

All 370 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 3977-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 1423 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 372 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. Published Ren and Ghosh quadratic exponential-sum estimates, when consumed, remain displayed raw theorem hypotheses; the progression-prefix estimate also remains an explicit unproved input. No own-paper analytic conclusion is assumed.

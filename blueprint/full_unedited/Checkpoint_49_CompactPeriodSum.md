# Checkpoint 49: Exact integer-sum interpretation of compact periodization

The integer-translate sum of a real symbol is proved one-periodic by an exact reindexing of the integer summation. For a symbol vanishing whenever |x|>=1, the infinite sum on the centered fundamental interval is proved equal to the three-term window. Every omitted integer translate is shown to vanish; no convergence or truncation error is assumed. This identifies the finite construction with genuine periodization, including both endpoints.


## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| CompactPeriodSum.lean | 2 |

- `integerPeriodSum_periodic`
- `integerPeriodSum_window`

<!-- checkpoint-verification -->

## Verification

All 116 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 3635-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 862 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 118 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. The already displayed raw progression-prefix estimate is consumed as a theorem hypothesis; it remains unproved. No new external analytic estimate or own-paper lemma is assumed.

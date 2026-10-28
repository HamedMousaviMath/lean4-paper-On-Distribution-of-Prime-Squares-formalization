# Checkpoint 85: The extra broad cutoff is redundant for the ordinary narrow term

For a positive narrow parameter Q with Q<=R, rational denominator q<=R and 2R^4<=N^2, multiplying the exact ordinary narrow cutoff by the broad dyadic cutoff leaves it unchanged. The proof applies the real cutoff-containment theorem with the actual log2(q) index and transports the identity to complex values. This justifies redundancy of the extra broad cutoff for the ordinary part in this range.


## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| OrdinaryLowContainment.lean | 1 |

- `ordinaryNarrowCutoff_mul_broad`

<!-- checkpoint-verification -->

## Verification

All 152 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 3671-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 931 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 154 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. The already displayed raw progression-prefix estimate is consumed as a theorem hypothesis; it remains unproved. No new external analytic estimate or own-paper lemma is assumed.

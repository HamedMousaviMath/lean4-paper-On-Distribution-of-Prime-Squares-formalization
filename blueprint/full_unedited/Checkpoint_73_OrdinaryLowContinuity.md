# Checkpoint 73: Continuity of the actual ordinary low-model ingredients

The actual ordinary rational model term and its arithmetic narrow cutoff are proved continuous in real frequency, at every positive arithmetic length. The power and phase integral are the genuine annular model already checked; the cutoff has its exact qN^2/Q dilation. No restriction on Q is needed for continuity because Lean's total division and the resulting constant dilations remain continuous.


## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| OrdinaryLowContinuity.lean | 2 |

- `rationalOrdinaryModelTerm_continuous`
- `ordinaryNarrowCutoff_continuous`

<!-- checkpoint-verification -->

## Verification

All 140 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 3659-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 911 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 142 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. The already displayed raw progression-prefix estimate is consumed as a theorem hypothesis; it remains unproved. No new external analytic estimate or own-paper lemma is assumed.

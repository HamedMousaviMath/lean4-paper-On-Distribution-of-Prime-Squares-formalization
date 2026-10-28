# Checkpoint 75: Continuity of the full arithmetic low term with both selectors

The full actual real-frequency low term, including both denominator selectors and ordinary and exceptional narrow cutoffs, is proved continuous. The selectors depend only on the fixed arithmetic data, so the proof treats their four cases and combines the already checked component regularity. This result prepares periodization of the low term; support containment and the source-specific low estimate remain separate obligations.


## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| LowModelContinuity.lean | 1 |

- `rationalLowModelTerm_continuous`

<!-- checkpoint-verification -->

## Verification

All 142 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 3661-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 914 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 144 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. The already displayed raw progression-prefix estimate is consumed as a theorem hypothesis; it remains unproved. No new external analytic estimate or own-paper lemma is assumed.

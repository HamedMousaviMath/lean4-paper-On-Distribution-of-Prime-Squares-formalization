# Checkpoint 50: Exact local agreement for narrow periodized symbols

When a real symbol vanishes already for |x|>=1/2, the two neighboring translates in the periodization window vanish throughout the closed centered interval. The resulting continuous circle symbol therefore agrees exactly with the original real symbol on [-1/2,1/2). This proves the absence of alias terms for sufficiently narrow cutoffs; the largest cutoff remains covered by the earlier three-translate formula. No periodicity of the original oscillatory integral is asserted.


## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| CompactCircleCore.lean | 2 |

- `compactPeriodWindow_small_support`
- `compactCircleLift_small_support_real`

<!-- checkpoint-verification -->

## Verification

All 117 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 3636-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 864 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 119 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. The already displayed raw progression-prefix estimate is consumed as a theorem hypothesis; it remains unproved. No new external analytic estimate or own-paper lemma is assumed.

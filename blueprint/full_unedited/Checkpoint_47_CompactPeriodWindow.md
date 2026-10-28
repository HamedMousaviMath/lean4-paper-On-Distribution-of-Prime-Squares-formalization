# Checkpoint 47: The finite periodization window and its endpoint compatibility

For a continuous real symbol supported inside [-1,1], periodization on the centered fundamental interval uses exactly the three translates f(x-1)+f(x)+f(x+1). The new proofs establish continuity, exact equality of the values at -1/2 and 1/2, and the uniform bound 3B when the original symbol has norm at most B. The endpoint identity includes the possible overlap at the largest cutoff scale; it is not assumed that only one translate contributes. These elementary analytic facts prepare a valid continuous circle symbol. They do not assert prime-distribution estimates.


## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| CompactPeriodWindow.lean | 3 |

- `compactPeriodWindow_continuous`
- `compactPeriodWindow_endpoints`
- `compactPeriodWindow_bound`

<!-- checkpoint-verification -->

## Verification

All 114 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 3633-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 858 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 116 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. The already displayed raw progression-prefix estimate is consumed as a theorem hypothesis; it remains unproved. No new external analytic estimate or own-paper lemma is assumed.

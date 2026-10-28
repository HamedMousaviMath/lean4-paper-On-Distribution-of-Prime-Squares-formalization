# Checkpoint 76: A compact continuous realization of the centered low symbol

The low term is given a continuous compact real-frequency realization by multiplying its exact centered source formula by the broad dyadic cutoff. Support inside [-1,1] is proved from the actual cutoff, for all parameters. This compactification is a defined candidate, not an unconditional assertion that the extra cutoff changes nothing. The previously proved narrow-within-broad geometry, and the later ordinary/exceptional containment identities, are required to identify it with the original source low formula in the admissible range.


## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| CenteredLowSymbol.lean | 2 |

- `sourceArcCutoffScale_zero_of_unit`
- `centeredLowSymbol_support`

<!-- checkpoint-verification -->

## Verification

All 143 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 3662-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 916 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 145 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. The already displayed raw progression-prefix estimate is consumed as a theorem hypothesis; it remains unproved. No new external analytic estimate or own-paper lemma is assumed.

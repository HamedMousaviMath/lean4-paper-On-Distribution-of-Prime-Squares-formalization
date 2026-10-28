# Checkpoint 80: Global finite low and high symbols with the actual annular error

Finite sums of the genuine low and high circle terms define continuous global finite low and high model symbols. Their sum equals the actual finite circle Gauss model. Adding the defined actual error gives exactly the annular von-Mangoldt averaging symbol, as an equality of continuous maps on the circle. This provides an unconditional candidate decomposition for the explicit finite center set; it does not supply the missing source-specific norm estimates or full minor-arc approximation.


## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| FiniteCircleHighLow.lean | 2 |

- `circleModel_low_add_high`
- `annularSymbol_circle_low_high_error`

<!-- checkpoint-verification -->

## Verification

All 147 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 3666-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 923 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 149 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. The already displayed raw progression-prefix estimate is consumed as a theorem hypothesis; it remains unproved. No new external analytic estimate or own-paper lemma is assumed.

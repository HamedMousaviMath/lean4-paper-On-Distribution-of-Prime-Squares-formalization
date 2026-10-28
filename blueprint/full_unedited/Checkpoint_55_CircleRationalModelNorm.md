# Checkpoint 55: Uniform Gauss decay survives actual circle periodization

The genuine centered rational model has the previously proved Gauss decay C_G q^(-5/12), uniformly in frequency, for N>=2, beta in [0,1] and exceptional coefficient of norm at most one. Its actual periodized circle term has bound 3 C_G q^(-5/12). The factor three accounts for the largest cutoff's possible aliases and is justified by the proved periodization estimate. C_G is the single unconditional constant already extracted from the formalized quadratic Gauss estimates; no prime-distribution input is added.


## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| CircleRationalModelNorm.lean | 2 |

- `centeredRationalSymbol_norm`
- `circleRationalModelTerm_norm`

<!-- checkpoint-verification -->

## Verification

All 122 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 3641-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 874 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 124 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. The already displayed raw progression-prefix estimate is consumed as a theorem hypothesis; it remains unproved. No new external analytic estimate or own-paper lemma is assumed.

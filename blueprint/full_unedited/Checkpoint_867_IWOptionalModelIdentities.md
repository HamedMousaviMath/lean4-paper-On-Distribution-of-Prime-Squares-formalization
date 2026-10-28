# Checkpoint 867: Exact optional Page model and actual IW low-symbol identities

The fixed-small/large-character split and the complete optional circle-model comparison are now exact identities of actual symbols. The low operator retains the original activity at each scale, and its fixed character term is identified with the actual cyclic square measure induced to the IW period. Lean proves the masked-denominator reindexing, the small/large optional split, and the original-minus-low decomposition. This supplies the exact same operator family required to combine the already checked comparison and changing-character maximal bounds.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| IWOptionalModelIdentities.lean | 6 |

- `largePageDatum_eq_some`
- `induced_annular_mask`
- `pageExceptionalAnnularSymbol_some`
- `page_exceptional_small_large_split`
- `page_model_IW_difference`
- `fixedPageIWSymbol_actual_measure`

<!-- checkpoint-verification -->

## Verification

All 934 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4553-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2581 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 936 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed source results under their paper hypotheses remain unchanged. Lemma 3.21, both conclusions of Theorems 1.1 and 1.3, all displayed clauses of Proposition 4.19 and both clauses of Proposition 6.21 are complete checked implications under their separately recorded independent deep inputs. The square-sign reflection is proved. Theorem 1.3 has actual finite sparse families, disjoint major subsets and the literal full all-cutoff maximum. The three general Section5 auxiliary statements remain partial, and the later Orlicz/ergodic/sieve applications remain unfinished. Proposition 4.19 consumes PrimeAsymptoticInputs, the refined PagePrimeSquareDistributionInputs c, RawPageUniquenessInput c and SmoothCircleBourgainInput C. These are independent raw analytic/data hypotheses, not own-paper operator conclusions or new Lean axioms. Theorem 1.1 retains its separately recorded older fixed-scale inputs and independent ordinary-square global decomposition; reflection is proved. Sparse applications additionally record OrdinarySquareStoppingInput CS and IndependentPrimeMaximalInput as explicit independent analytic boundaries. Their existence and the exact normalization/support/sign adaptations remain unproved; neither predicate contains this paper's endpoint or sparse conclusion. Section7 additionally records the independent RawTaoArcConstructionInput C, used only to obtain actual finite IW frequency geometry. Its existence is unproved; multiplier, sampling, low and high norm estimates are not fields and remain unfinished.

# Checkpoint 793: Construct actual disjoint major subsets and retain them under dilation

Proves that deleting the union of strict descendants in a finite laminar interval family gives actual pairwise disjoint major subsets, with the cardinality prescribed by the packing inequality. Proves fivefold dilation preserves those very subsets while dividing the sparsity constant exactly by five. Thus a 3/4-sparse parent family produces a genuine 1/10-sparse family of fivefold intervals, with no unproved grid replacement. The construction of the stopping intervals and the analytic local estimates remain separate unfinished deductions.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| FiniteSparseMajorSets.lean | 7 |

- `integerMajorCore_subset`
- `integerMajorCore_disjoint_descendant`
- `integerMajorCore_pairwise`
- `integerMajorCore_card`
- `integerSparseFamily_of_laminar`
- `integerSparseFamily_five`
- `integerSparseFamily_five_source`

<!-- checkpoint-verification -->

## Verification

All 860 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4467-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2232 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 862 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results under their paper hypotheses remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. Lemma 3.21, both conclusions of Theorem 1.1, all displayed clauses of Proposition 4.19 and both clauses of Proposition 6.21 are complete checked implications under their separately recorded independent deep inputs. The square-sign reflection is proved. The whole paper, the stronger printed auxiliary lemmas and the later sparse/ergodic/sieve applications remain unfinished. Proposition 4.19 consumes PrimeAsymptoticInputs, the refined PagePrimeSquareDistributionInputs c, RawPageUniquenessInput c and SmoothCircleBourgainInput C. These are independent raw analytic/data hypotheses, not own-paper operator conclusions or new Lean axioms. Theorem 1.1 retains its separately recorded older fixed-scale inputs and independent ordinary-square global decomposition; reflection is proved.

# Checkpoint 797: Prove termination and sparse cost summation of the finite stopping recursion

Proves termination and cost summation of finite interval stopping recursion by strong induction on integer length. A one-generation recursive inequality and quarter-packing produce a finite family with actual 3/4-sized pairwise disjoint major subsets and the required summed cost. The local one-generation inequality is explicitly a hypothesis of this abstract theorem and still has to be proved for the actual averages; it is not declared an external analytic input or the completed paper recursion.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| FiniteSparseRecursion.lean | 3 |

- `integerLaminar_subset`
- `finiteSparseRecursion_certificate`
- `finiteSparseRecursion`

<!-- checkpoint-verification -->

## Verification

All 864 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4471-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2246 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 866 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results under their paper hypotheses remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. Lemma 3.21, both conclusions of Theorem 1.1, all displayed clauses of Proposition 4.19 and both clauses of Proposition 6.21 are complete checked implications under their separately recorded independent deep inputs. The square-sign reflection is proved. The whole paper, the stronger printed auxiliary lemmas and the later sparse/ergodic/sieve applications remain unfinished. Proposition 4.19 consumes PrimeAsymptoticInputs, the refined PagePrimeSquareDistributionInputs c, RawPageUniquenessInput c and SmoothCircleBourgainInput C. These are independent raw analytic/data hypotheses, not own-paper operator conclusions or new Lean axioms. Theorem 1.1 retains its separately recorded older fixed-scale inputs and independent ordinary-square global decomposition; reflection is proved.

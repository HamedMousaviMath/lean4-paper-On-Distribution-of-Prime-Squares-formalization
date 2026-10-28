# Checkpoint 801: Construct maximal consecutive bad intervals and prove their exact disjoint covering

Constructs the finite collection of every nonempty integer subinterval of a parent, with an exact membership characterization. Constructs maximal consecutive component intervals of a finite bad set, proves that they cover that set exactly and are pairwise disjoint, and proves their inclusion in the parent. These are actual intervals and finite sets, not a chosen abstract partition.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| FiniteIntegerSubintervals.lean | 7 |

- `mem_integerSubintervals`
- `integerSubintervals_self`
- `integerSubintervals_trans`
- `integerSingletonInterval_points`
- `integerMaximalComponents_subset`
- `integerMaximalComponents_cover`
- `integerMaximalComponents_disjoint`

<!-- checkpoint-verification -->

## Verification

All 868 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4475-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2270 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 870 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results under their paper hypotheses remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. Lemma 3.21, both conclusions of Theorem 1.1, all displayed clauses of Proposition 4.19 and both clauses of Proposition 6.21 are complete checked implications under their separately recorded independent deep inputs. The square-sign reflection is proved. The whole paper, the stronger printed auxiliary lemmas and the later sparse/ergodic/sieve applications remain unfinished. Proposition 4.19 consumes PrimeAsymptoticInputs, the refined PagePrimeSquareDistributionInputs c, RawPageUniquenessInput c and SmoothCircleBourgainInput C. These are independent raw analytic/data hypotheses, not own-paper operator conclusions or new Lean axioms. Theorem 1.1 retains its separately recorded older fixed-scale inputs and independent ordinary-square global decomposition; reflection is proved.

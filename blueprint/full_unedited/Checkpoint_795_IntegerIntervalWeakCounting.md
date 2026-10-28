# Checkpoint 795: Prove the finite weak density bound and quantitative stopping packing

Proves the counting-measure weak (1,1) inequality for the union of all intervals in a finite family whose F-density exceeds a given threshold. The constant is 3 and follows from the checked disjoint interval selection and exact finite intersection counts. Derives a concrete stopping packing bound: at threshold 64|F|/L the bad union has cardinality at most L/4. This supplies the quantitative packing ingredient without assuming a maximal-function theorem.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| IntegerIntervalWeakCounting.lean | 4 |

- `disjoint_interval_intersection_count`
- `integerInterval_weak_counting`
- `integerBadIntervalUnion_counting`
- `integerBadIntervalUnion_packing`

<!-- checkpoint-verification -->

## Verification

All 862 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4469-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2239 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 864 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results under their paper hypotheses remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. Lemma 3.21, both conclusions of Theorem 1.1, all displayed clauses of Proposition 4.19 and both clauses of Proposition 6.21 are complete checked implications under their separately recorded independent deep inputs. The square-sign reflection is proved. The whole paper, the stronger printed auxiliary lemmas and the later sparse/ergodic/sieve applications remain unfinished. Proposition 4.19 consumes PrimeAsymptoticInputs, the refined PagePrimeSquareDistributionInputs c, RawPageUniquenessInput c and SmoothCircleBourgainInput C. These are independent raw analytic/data hypotheses, not own-paper operator conclusions or new Lean axioms. Theorem 1.1 retains its separately recorded older fixed-scale inputs and independent ordinary-square global decomposition; reflection is proved.

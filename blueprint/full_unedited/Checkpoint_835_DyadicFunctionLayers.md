# Checkpoint 835: Actual finite dyadic layers and exact cost partition

The finite dyadic layer decomposition is constructed for arbitrary complex finitely supported inputs. A chosen integer height satisfies the exact dyadic bracketing; layers are actual finite subsets, pairwise disjoint, and their indices form a finite set. Lean proves exact partition of layer costs and pointwise domination of the input by the bounded remainder plus the weighted indicators. The half-open convention at dyadic boundary values is explicit, and does not discard points. This step is algebraic and does not assume a restricted weak estimate.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| DyadicFunctionLayers.lean | 7 |

- `functionLayerIndex_spec`
- `functionLayer_mem`
- `functionLayer_disjoint`
- `functionLayer_nonempty_index`
- `functionLayer_bounds`
- `functionLayer_partition_cost`
- `functionLayer_majorization`

<!-- checkpoint-verification -->

## Verification

All 902 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4509-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2428 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 904 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed source results under their paper hypotheses remain unchanged. Lemma 3.21, both conclusions of Theorems 1.1 and 1.3, all displayed clauses of Proposition 4.19 and both clauses of Proposition 6.21 are complete checked implications under their separately recorded independent deep inputs. The square-sign reflection is proved. Theorem 1.3 has actual finite sparse families, disjoint major subsets and the literal full all-cutoff maximum. The three general Section5 auxiliary statements remain partial, and the later Orlicz/ergodic/sieve applications remain unfinished. Proposition 4.19 consumes PrimeAsymptoticInputs, the refined PagePrimeSquareDistributionInputs c, RawPageUniquenessInput c and SmoothCircleBourgainInput C. These are independent raw analytic/data hypotheses, not own-paper operator conclusions or new Lean axioms. Theorem 1.1 retains its separately recorded older fixed-scale inputs and independent ordinary-square global decomposition; reflection is proved. Sparse applications additionally record OrdinarySquareStoppingInput CS and IndependentPrimeMaximalInput as explicit independent analytic boundaries. Their existence and the exact normalization/support/sign adaptations remain unproved; neither predicate contains this paper's endpoint or sparse conclusion.

# Checkpoint 821: Control the literal all-cutoff full prime-square maximum by the finite root

Defines the literal countable full maximal indicator over every original integer cutoff N>=2 and proves its range is bounded and it dominates each cutoff. Proves positive-kernel comparison with a nearby dyadic full cutoff, then controls every full dyadic cutoff by the finite annular root through the exact full-to-annular identity. The resulting actual maximal pairing is at most four times the finite localized root pairing. No large-scale truncation, limiting sparse-family selection or maximal Lp hypothesis is used for this reduction.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| PrimeFullMaximalComparison.lean | 10 |

- `fullPrimeKernel_cutoff_bound`
- `fullPrimeIndicator_cutoff_bound`
- `primeSparseRoot_full_dyadic`
- `primeSparseRoot_full_cutoff`
- `primeSquareAverageValue_indicator_kernel`
- `primeSquareMaximalIndicator_bdd`
- `primeSquareMaximalIndicator_dominates`
- `primeSquareMaximalIndicator_nonneg`
- `primeSquareMaximalPairing_nonneg`
- `primeSquareMaximalPairing_le_root`

<!-- checkpoint-verification -->

## Verification

All 888 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4495-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2348 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 890 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results under their paper hypotheses remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. Lemma 3.21, both conclusions of Theorem 1.1, all displayed clauses of Proposition 4.19 and both clauses of Proposition 6.21 are complete checked implications under their separately recorded independent deep inputs. The square-sign reflection is proved. The whole paper, the stronger printed auxiliary lemmas and the later sparse/ergodic/sieve applications remain unfinished. Proposition 4.19 consumes PrimeAsymptoticInputs, the refined PagePrimeSquareDistributionInputs c, RawPageUniquenessInput c and SmoothCircleBourgainInput C. These are independent raw analytic/data hypotheses, not own-paper operator conclusions or new Lean axioms. Theorem 1.1 retains its separately recorded older fixed-scale inputs and independent ordinary-square global decomposition; reflection is proved. Sparse applications additionally record OrdinarySquareStoppingInput CS and IndependentPrimeMaximalInput as explicit independent analytic boundaries. Their existence and the exact normalization/support/sign adaptations remain unproved; neither predicate contains this paper's endpoint or sparse conclusion.

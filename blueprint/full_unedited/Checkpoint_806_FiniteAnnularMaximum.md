# Checkpoint 806: Define and control actual truncated dyadic prime-square maxima

Defines the actual finite dyadic annular prime-square maximum with arithmetic cutoff 2^j*2 and spatial cutoff N^2<=L. Proves exact index coverage, monotonicity, attainment on nonempty finite scale sets, elementary maximum bounds and nonnegativity of the localized finite maximal pairing. The zero-scale convention is an actual nonnegative finite supremum.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| FiniteAnnularMaximum.lean | 9 |

- `mem_dyadicSpatialIndices`
- `dyadicSpatialIndices_mono`
- `dyadicSpatialIndices_empty`
- `finiteAnnularMaximum_dominates`
- `finiteAnnularMaximum_mono`
- `finiteAnnularMaximum_attained`
- `finiteAnnularMaximum_le`
- `finiteAnnularMaximum_union`
- `annularLocalMaxPairing_nonneg`

<!-- checkpoint-verification -->

## Verification

All 873 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4480-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2300 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 875 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results under their paper hypotheses remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. Lemma 3.21, both conclusions of Theorem 1.1, all displayed clauses of Proposition 4.19 and both clauses of Proposition 6.21 are complete checked implications under their separately recorded independent deep inputs. The square-sign reflection is proved. The whole paper, the stronger printed auxiliary lemmas and the later sparse/ergodic/sieve applications remain unfinished. Proposition 4.19 consumes PrimeAsymptoticInputs, the refined PagePrimeSquareDistributionInputs c, RawPageUniquenessInput c and SmoothCircleBourgainInput C. These are independent raw analytic/data hypotheses, not own-paper operator conclusions or new Lean axioms. Theorem 1.1 retains its separately recorded older fixed-scale inputs and independent ordinary-square global decomposition; reflection is proved.

# Checkpoint 848: Actual real-line Fourier multipliers and Lp norm interfaces

The real-line Fourier multiplier is now an actual continuous linear operator on real-line L2, built from Mathlib's unitary Fourier transform, multiplication by a bounded continuous symbol, and inverse Fourier transform. Lean proves the Fourier identity and symbol-norm operator bounds. General-p real and integer multiplier bounds require both Lp membership and the explicit extended-norm inequality on the L2 intersection; neither bound is assumed merely by declaring its predicate. The newly needed pinned Mathlib Fourier Lp dependency was compiled from the unchanged pinned sources (dependency build log retained). This checkpoint provides the actual operator interface for a general independent IW theorem, but does not yet prove the current paper's quantitative low/high or restricted maximal estimate.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| RealLineFourierMultipliers.lean | 14 |

- `realLineProduct_memLp`
- `realLineMultiplyValue_ae`
- `realLineMultiplyValue_norm_le`
- `realLineMultiply_ae`
- `realLineMultiply_norm_le`
- `realLineMultiply_opNorm_le`
- `realLineMultiply_opNorm_le_of_bound`
- `realLineMultiplier_apply`
- `realLineFourier_multiplier`
- `realLineMultiplier_norm_le`
- `realLineMultiplier_opNorm_le`
- `realLineMultiplier_opNorm_le_of_bound`
- `realLpMultiplierBound_mono`
- `integerLpMultiplierBound_mono`

<!-- checkpoint-verification -->

## Verification

All 915 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4534-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2498 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 917 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed source results under their paper hypotheses remain unchanged. Lemma 3.21, both conclusions of Theorems 1.1 and 1.3, all displayed clauses of Proposition 4.19 and both clauses of Proposition 6.21 are complete checked implications under their separately recorded independent deep inputs. The square-sign reflection is proved. Theorem 1.3 has actual finite sparse families, disjoint major subsets and the literal full all-cutoff maximum. The three general Section5 auxiliary statements remain partial, and the later Orlicz/ergodic/sieve applications remain unfinished. Proposition 4.19 consumes PrimeAsymptoticInputs, the refined PagePrimeSquareDistributionInputs c, RawPageUniquenessInput c and SmoothCircleBourgainInput C. These are independent raw analytic/data hypotheses, not own-paper operator conclusions or new Lean axioms. Theorem 1.1 retains its separately recorded older fixed-scale inputs and independent ordinary-square global decomposition; reflection is proved. Sparse applications additionally record OrdinarySquareStoppingInput CS and IndependentPrimeMaximalInput as explicit independent analytic boundaries. Their existence and the exact normalization/support/sign adaptations remain unproved; neither predicate contains this paper's endpoint or sparse conclusion. Section7 additionally records the independent RawTaoArcConstructionInput C, used only to obtain actual finite IW frequency geometry. Its existence is unproved; multiplier, sampling, low and high norm estimates are not fields and remain unfinished.

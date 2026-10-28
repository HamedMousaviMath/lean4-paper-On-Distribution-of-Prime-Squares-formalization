# Checkpoint 858: Actual quantitative IW common-cutoff denominator-tail maximum

The common-cutoff tail is now specialized to the exact quantitative IW parameters and the actual cyclic square measures. Lean proves that epsilon^(-1) lies inside every needed denominator-band core, then combines the actual frequency geometry and the proved uniform cyclic Gauss decay to obtain a countable dyadic L2 majorant of size K*Q^(-1/4). The constant is uniform in r,k,Q, period, complex character and variable beta. This proves the common-cutoff denominator-tail contribution for both the principal and any fixed induced character. It does not require the external IW multiplier theorem or assume the low-model maximum; only the previously declared generic smooth multifrequency input is used.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| IWCommonCutoffTails.lean | 4 |

- `iwCutoffScale_formula`
- `iwCutoffScale_four_le`
- `iwCutoffScale_band_core`
- `iw_cyclic_square_common_tail`

<!-- checkpoint-verification -->

## Verification

All 925 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4544-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2542 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 927 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed source results under their paper hypotheses remain unchanged. Lemma 3.21, both conclusions of Theorems 1.1 and 1.3, all displayed clauses of Proposition 4.19 and both clauses of Proposition 6.21 are complete checked implications under their separately recorded independent deep inputs. The square-sign reflection is proved. Theorem 1.3 has actual finite sparse families, disjoint major subsets and the literal full all-cutoff maximum. The three general Section5 auxiliary statements remain partial, and the later Orlicz/ergodic/sieve applications remain unfinished. Proposition 4.19 consumes PrimeAsymptoticInputs, the refined PagePrimeSquareDistributionInputs c, RawPageUniquenessInput c and SmoothCircleBourgainInput C. These are independent raw analytic/data hypotheses, not own-paper operator conclusions or new Lean axioms. Theorem 1.1 retains its separately recorded older fixed-scale inputs and independent ordinary-square global decomposition; reflection is proved. Sparse applications additionally record OrdinarySquareStoppingInput CS and IndependentPrimeMaximalInput as explicit independent analytic boundaries. Their existence and the exact normalization/support/sign adaptations remain unproved; neither predicate contains this paper's endpoint or sparse conclusion. Section7 additionally records the independent RawTaoArcConstructionInput C, used only to obtain actual finite IW frequency geometry. Its existence is unproved; multiplier, sampling, low and high norm estimates are not fields and remain unfinished.

# Checkpoint 923: Normalized cyclic Lp bounds and actual finite-cyclic Young inequality

Lean proves the normalized cyclic real-Lp norm inequalities used in the large-scale sampling argument: fibrewise norm comparison, invariance under cyclic translations, triangle inequality, scalar multiplication and finite sums. For the literal cyclic convolution of arbitrary Schwartz fibres, the resulting norm is at most the actual cyclic total variation times the original norm. The normalization is explicit, all relevant fibre memberships are checked, and no factor depending on the period is lost. These elementary analytic steps are proved rather than included in a new external input. The actual finite-input Fourier lift and narrow real-variable maximal application remain next.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| CyclicRealLpBounds.lean | 9 |

- `cyclicRealLpSize_mono_bound`
- `eLpNorm_count_equiv`
- `cyclicRealLpSize_translate`
- `cyclicRealLpSize_add`
- `cyclicRealLpSize_smul`
- `cyclicRealLpSize_zero`
- `cyclicRealLpSize_finsetSum`
- `cyclicConvolutionSchwartz_apply`
- `cyclicConvolutionSchwartz_Lp`

<!-- checkpoint-verification -->

## Verification

All 990 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4610-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2785 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 992 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed source results under their paper hypotheses remain unchanged. Lemma 3.21, both conclusions of Theorems 1.1 and 1.3, all displayed clauses of Proposition 4.19 and both clauses of Proposition 6.21 are complete checked implications under their separately recorded independent deep inputs. The square-sign reflection is proved. Theorem 1.3 has actual finite sparse families, disjoint major subsets and the literal full all-cutoff maximum. The three general Section5 auxiliary statements remain partial, and the later Orlicz/ergodic/sieve applications remain unfinished. Earlier Theorems1.1/1.3 and Propositions4.19/6.21 preserve their separately recorded raw prime/distribution, Page, generic smooth multifrequency, ordinary-square and stopping hypotheses. Section7 additionally records RawTaoArcConstructionInput C and RawIWMultiplierInput C as explicit unproved independent general theorems, not Lean axioms. Actual geometry and full goodness and conditional smooth multiplier specialization are proved. The actual prime high-side comparison uses raw Tao construction, SmoothCircleBourgainInput, RawPageUniquenessInput and PagePrimeSquareDistributionInputs; its own coefficient identities, cutoffs, Page selection and approximation deductions are proved. General sampling and concrete continuous/low estimates remain unfinished. The current-paper low maximum, restricted estimate and full high/low conclusion are not external input fields.

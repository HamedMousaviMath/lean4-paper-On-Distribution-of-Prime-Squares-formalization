# Checkpoint 879: Actual continuous annular kernel, integrability and Hardy-Littlewood box bound

The literal continuous annular kernel is now a concrete real density supported on [N^2/4,N^2]. Lean proves its real and complex integrability, positivity and the uniform box bound by N^(-2) on [0,N^2] for N>=2 and beta<=1. This is the own-paper kernel bound needed to apply a precise general Hardy-Littlewood theorem; no continuous maximal estimate is assumed. Its exact Fourier-transform identity and uniform signed-kernel regularity remain subsequent obligations. The current canonical progress, statement review, independent-boundary and recovery reports have also been saved with the checked878 scope.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| ContinuousAnnularKernel.lean | 8 |

- `continuousAnnularKernel_of_mem`
- `continuousAnnularKernel_of_not_mem`
- `annularKernelDensity_continuousOn`
- `continuousAnnularKernel_integrable`
- `continuousAnnularKernel_complex_integrable`
- `continuousAnnularKernel_nonneg`
- `annularKernelDensity_bound`
- `continuousAnnularKernel_box_bound`

<!-- checkpoint-verification -->

## Verification

All 946 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4565-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2635 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 948 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed source results under their paper hypotheses remain unchanged. Lemma 3.21, both conclusions of Theorems 1.1 and 1.3, all displayed clauses of Proposition 4.19 and both clauses of Proposition 6.21 are complete checked implications under their separately recorded independent deep inputs. The square-sign reflection is proved. Theorem 1.3 has actual finite sparse families, disjoint major subsets and the literal full all-cutoff maximum. The three general Section5 auxiliary statements remain partial, and the later Orlicz/ergodic/sieve applications remain unfinished. Earlier Theorems1.1/1.3 and Propositions4.19/6.21 preserve their separately recorded raw prime/distribution, Page, generic smooth multifrequency, ordinary-square and stopping hypotheses. Section7 additionally records RawTaoArcConstructionInput C and RawIWMultiplierInput C as explicit unproved independent general theorems, not Lean axioms. Actual geometry and full goodness and conditional smooth multiplier specialization are proved. The actual prime high-side comparison uses raw Tao construction, SmoothCircleBourgainInput, RawPageUniquenessInput and PagePrimeSquareDistributionInputs; its own coefficient identities, cutoffs, Page selection and approximation deductions are proved. General sampling and concrete continuous/low estimates remain unfinished. The current-paper low maximum, restricted estimate and full high/low conclusion are not external input fields.

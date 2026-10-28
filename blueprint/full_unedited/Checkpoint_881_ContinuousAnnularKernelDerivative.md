# Checkpoint 881: Uniform derivative bound for the actual continuous annular density

Lean now proves the derivative formula for the actual annular density and the uniform bound |K'_N(x)|<=4/N^4 on its annulus for 0<=beta<=1 and N>=2. The derivative is also identified exactly as (beta/2-1) times the density divided by x. Together with the checked support, box bound, integrability and exact Fourier identity, this supplies the own-paper local regularity data for the remaining uniform kernel argument. No full Calderon-Zygmund applicability, general-p increment estimate or low maximum is assumed or claimed.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| ContinuousAnnularKernelDerivative.lean | 3 |

- `annularKernelDensity_hasDerivAt`
- `annularKernelDerivative_density`
- `annularKernelDerivative_bound`

<!-- checkpoint-verification -->

## Verification

All 948 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4567-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2640 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 950 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed source results under their paper hypotheses remain unchanged. Lemma 3.21, both conclusions of Theorems 1.1 and 1.3, all displayed clauses of Proposition 4.19 and both clauses of Proposition 6.21 are complete checked implications under their separately recorded independent deep inputs. The square-sign reflection is proved. Theorem 1.3 has actual finite sparse families, disjoint major subsets and the literal full all-cutoff maximum. The three general Section5 auxiliary statements remain partial, and the later Orlicz/ergodic/sieve applications remain unfinished. Earlier Theorems1.1/1.3 and Propositions4.19/6.21 preserve their separately recorded raw prime/distribution, Page, generic smooth multifrequency, ordinary-square and stopping hypotheses. Section7 additionally records RawTaoArcConstructionInput C and RawIWMultiplierInput C as explicit unproved independent general theorems, not Lean axioms. Actual geometry and full goodness and conditional smooth multiplier specialization are proved. The actual prime high-side comparison uses raw Tao construction, SmoothCircleBourgainInput, RawPageUniquenessInput and PagePrimeSquareDistributionInputs; its own coefficient identities, cutoffs, Page selection and approximation deductions are proved. General sampling and concrete continuous/low estimates remain unfinished. The current-paper low maximum, restricted estimate and full high/low conclusion are not external input fields.

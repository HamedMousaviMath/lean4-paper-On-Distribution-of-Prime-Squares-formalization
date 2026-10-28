# Checkpoint 887: Uniform dyadic sum of actual annular far-translation integrals

Lean sums the actual far-translation integrals over every finite set of consecutive dyadic scales. Scales starting at N=2 have total at most 70/3, using the checked min(y,1/y) dyadic profile. Including N=1 costs at most 2, with no dependence on the number of scales, beta or the translation. The zero-translation case is handled exactly. This is the uniform kernel regularity needed for arbitrary bounded signed increments; assembling that signed kernel and its precise Fourier symbol is next.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| ContinuousAnnularDyadicTranslation.lean | 3 |

- `dyadic_annular_translation_ratio`
- `annularFarTranslation_dyadic_sum`
- `annularFarTranslation_all_dyadic_sum`

<!-- checkpoint-verification -->

## Verification

All 954 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4573-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2659 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 956 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed source results under their paper hypotheses remain unchanged. Lemma 3.21, both conclusions of Theorems 1.1 and 1.3, all displayed clauses of Proposition 4.19 and both clauses of Proposition 6.21 are complete checked implications under their separately recorded independent deep inputs. The square-sign reflection is proved. Theorem 1.3 has actual finite sparse families, disjoint major subsets and the literal full all-cutoff maximum. The three general Section5 auxiliary statements remain partial, and the later Orlicz/ergodic/sieve applications remain unfinished. Earlier Theorems1.1/1.3 and Propositions4.19/6.21 preserve their separately recorded raw prime/distribution, Page, generic smooth multifrequency, ordinary-square and stopping hypotheses. Section7 additionally records RawTaoArcConstructionInput C and RawIWMultiplierInput C as explicit unproved independent general theorems, not Lean axioms. Actual geometry and full goodness and conditional smooth multiplier specialization are proved. The actual prime high-side comparison uses raw Tao construction, SmoothCircleBourgainInput, RawPageUniquenessInput and PagePrimeSquareDistributionInputs; its own coefficient identities, cutoffs, Page selection and approximation deductions are proved. General sampling and concrete continuous/low estimates remain unfinished. The current-paper low maximum, restricted estimate and full high/low conclusion are not external input fields.

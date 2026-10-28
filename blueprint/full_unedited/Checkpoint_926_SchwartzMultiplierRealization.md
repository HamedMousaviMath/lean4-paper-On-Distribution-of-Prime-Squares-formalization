# Checkpoint 926: Actual Schwartz realization of real multipliers and cyclic norm transfer

Lean identifies the actual real L2 Fourier multiplier with the corresponding Schwartz function whenever their literal Fourier transforms agree. Its general Lp multiplier bound therefore controls the actual Schwartz representative, with both input and output almost-everywhere identities checked. Compact smooth multipliers are constructed on arbitrary Schwartz functions by their genuine inverse Fourier transform, their exact Fourier formula and Lp bound are proved, and the latter lifts to the normalized cyclic family norm. This removes a possible gap between abstract L2 operator norms and the pointwise functions later sampled. No additional external analytic input is introduced.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| SchwartzMultiplierRealization.lean | 6 |

- `realLineFourier_schwartz`
- `realLineMultiplier_schwartz_of_fourier`
- `realLpMultiplierBound_on_schwartz`
- `compactSmoothMultiplier_fourier`
- `compactSmoothMultiplier_Lp`
- `cyclicRealLpSize_compactMultiplier`

<!-- checkpoint-verification -->

## Verification

All 993 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4613-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2812 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 995 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed source results under their paper hypotheses remain unchanged. Lemma 3.21, both conclusions of Theorems 1.1 and 1.3, all displayed clauses of Proposition 4.19 and both clauses of Proposition 6.21 are complete checked implications under their separately recorded independent deep inputs. The square-sign reflection is proved. Theorem 1.3 has actual finite sparse families, disjoint major subsets and the literal full all-cutoff maximum. The three general Section5 auxiliary statements remain partial, and the later Orlicz/ergodic/sieve applications remain unfinished. Earlier Theorems1.1/1.3 and Propositions4.19/6.21 preserve their separately recorded raw prime/distribution, Page, generic smooth multifrequency, ordinary-square and stopping hypotheses. Section7 additionally records RawTaoArcConstructionInput C and RawIWMultiplierInput C as explicit unproved independent general theorems, not Lean axioms. Actual geometry and full goodness and conditional smooth multiplier specialization are proved. The actual prime high-side comparison uses raw Tao construction, SmoothCircleBourgainInput, RawPageUniquenessInput and PagePrimeSquareDistributionInputs; its own coefficient identities, cutoffs, Page selection and approximation deductions are proved. General sampling and concrete continuous/low estimates remain unfinished. The current-paper low maximum, restricted estimate and full high/low conclusion are not external input fields.

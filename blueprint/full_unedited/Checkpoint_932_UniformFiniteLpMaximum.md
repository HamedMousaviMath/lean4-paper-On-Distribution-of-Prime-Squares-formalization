# Checkpoint 932: General uniform finite to countable actual Lp maximal extension

Lean proves a general uniform-finite-to-countable Lp maximal extension on the integers for every nonzero exponent, including infinity. A finite uniform extended-norm bound for every literal finite coordinate maximum yields one nonnegative actual Lp majorant dominating every member at every integer, with the same bound. Pointwise boundedness follows from counting-measure coordinate control; the convergence of finite maxima and the norm passage use the pinned Mathlib monotone-convergence and Fatou results with their hypotheses checked. No additional external theorem is introduced. This extends the newly checked narrow IW finite maxima to a genuine countable maximum.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| UniformFiniteLpMaximum.lean | 1 |

- `uniform_finite_integer_Lp_majorant`

<!-- checkpoint-verification -->

## Verification

All 999 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4621-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2834 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1001 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed source results under their paper hypotheses remain unchanged. Lemma 3.21, both conclusions of Theorems 1.1 and 1.3, all displayed clauses of Proposition 4.19 and both clauses of Proposition 6.21 are complete checked implications under their separately recorded independent deep inputs. The square-sign reflection is proved. Theorem 1.3 has actual finite sparse families, disjoint major subsets and the literal full all-cutoff maximum. The three general Section5 auxiliary statements remain partial, and the later Orlicz/ergodic/sieve applications remain unfinished. Earlier Theorems1.1/1.3 and Propositions4.19/6.21 preserve their separately recorded raw prime/distribution, Page, generic smooth multifrequency, ordinary-square and stopping hypotheses. Section7 additionally records RawTaoArcConstructionInput C and RawIWMultiplierInput C as explicit unproved independent general theorems, not Lean axioms. Actual geometry and full goodness and conditional smooth multiplier specialization are proved. The actual prime high-side comparison uses raw Tao construction, SmoothCircleBourgainInput, RawPageUniquenessInput and PagePrimeSquareDistributionInputs; its own coefficient identities, cutoffs, Page selection and approximation deductions are proved. General sampling and concrete continuous/low estimates remain unfinished. The current-paper low maximum, restricted estimate and full high/low conclusion are not external input fields.

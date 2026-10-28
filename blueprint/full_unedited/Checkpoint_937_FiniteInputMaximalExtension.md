# Checkpoint 937: All-input extension and literal countable integer Lp maxima

Lean proves a general finite-input-to-all-input extension for countable families of actual bounded integer L2 operators. Finite inputs converge to the original L2 input, each finite output maximum is continuous, truncating the input does not increase its counting-measure Lp norm, and the checked Fatou and finite-to-countable principles preserve the exact maximal constant. This extends a proved finite-input maximal bound, not an independently assumed own-paper conclusion. The resulting all-input property implies the literal countable maximum bound and the standard integer lp formulation for every positive finite p<=2, using the exact counting-norm bridge and canonical integer lp inclusion into l2. No additional external analytic theorem is introduced.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| FiniteInputMaximalExtension.lean | 4 |

- `finiteInputLp_count_norm_le`
- `finite_input_maximal_extension`
- `allInputLpMaximalBound_integerLp`
- `allInputLpMaximalBound_maximum`

<!-- checkpoint-verification -->

## Verification

All 1004 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4626-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2855 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1006 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed source results under their paper hypotheses remain unchanged. Lemma 3.21, both conclusions of Theorems 1.1 and 1.3, all displayed clauses of Proposition 4.19 and both clauses of Proposition 6.21 are complete checked implications under their separately recorded independent deep inputs. The square-sign reflection is proved. Theorem 1.3 has actual finite sparse families, disjoint major subsets and the literal full all-cutoff maximum. The three general Section5 auxiliary statements remain partial, and the later Orlicz/ergodic/sieve applications remain unfinished. Earlier Theorems1.1/1.3 and Propositions4.19/6.21 preserve their separately recorded raw prime/distribution, Page, generic smooth multifrequency, ordinary-square and stopping hypotheses. Section7 additionally records RawTaoArcConstructionInput C and RawIWMultiplierInput C as explicit unproved independent general theorems, not Lean axioms. Actual geometry and full goodness and conditional smooth multiplier specialization are proved. The actual prime high-side comparison uses raw Tao construction, SmoothCircleBourgainInput, RawPageUniquenessInput and PagePrimeSquareDistributionInputs; its own coefficient identities, cutoffs, Page selection and approximation deductions are proved. General sampling and concrete continuous/low estimates remain unfinished. The current-paper low maximum, restricted estimate and full high/low conclusion are not external input fields.

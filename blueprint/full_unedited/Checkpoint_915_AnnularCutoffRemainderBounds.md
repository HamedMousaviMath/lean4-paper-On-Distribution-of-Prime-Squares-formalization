# Checkpoint 915: Actual cutoff remainder identities smoothness and L1/L2 endpoint bounds

Lean proves the actual original-minus-narrow annular cutoff remainder: exact nested-cutoff core and product identities, literal remainder factorization, uniform domination by the actual annular Fourier symbol, C-infinity smoothness, and the sharper L2 decay 4b/(pi N^2). The general-p rough bound 2*cutoffL1Constant follows from the checked individual Young bounds and actual operator subtraction; no own remainder norm is assumed. All endpoint applicability is now checked. Interpolation through the separately recorded general Riesz-Thorin theorem and subsequent IW transfer/summation are next.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| AnnularCutoffRemainderBounds.lean | 8 |

- `sourceArcCutoff_nested_core`
- `sourceArcCutoff_nested_product`
- `annularCutoffRemainderSymbol_factor`
- `annularCutoffRemainderSymbol_norm_le`
- `annularCutoffRemainderSymbol_decay`
- `annularCutoffRemainderSymbol_smooth`
- `annularCutoffRemainder_Lp_rough`
- `annularCutoffRemainder_L2`

<!-- checkpoint-verification -->

## Verification

All 982 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4601-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2754 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 984 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed source results under their paper hypotheses remain unchanged. Lemma 3.21, both conclusions of Theorems 1.1 and 1.3, all displayed clauses of Proposition 4.19 and both clauses of Proposition 6.21 are complete checked implications under their separately recorded independent deep inputs. The square-sign reflection is proved. Theorem 1.3 has actual finite sparse families, disjoint major subsets and the literal full all-cutoff maximum. The three general Section5 auxiliary statements remain partial, and the later Orlicz/ergodic/sieve applications remain unfinished. Earlier Theorems1.1/1.3 and Propositions4.19/6.21 preserve their separately recorded raw prime/distribution, Page, generic smooth multifrequency, ordinary-square and stopping hypotheses. Section7 additionally records RawTaoArcConstructionInput C and RawIWMultiplierInput C as explicit unproved independent general theorems, not Lean axioms. Actual geometry and full goodness and conditional smooth multiplier specialization are proved. The actual prime high-side comparison uses raw Tao construction, SmoothCircleBourgainInput, RawPageUniquenessInput and PagePrimeSquareDistributionInputs; its own coefficient identities, cutoffs, Page selection and approximation deductions are proved. General sampling and concrete continuous/low estimates remain unfinished. The current-paper low maximum, restricted estimate and full high/low conclusion are not external input fields.

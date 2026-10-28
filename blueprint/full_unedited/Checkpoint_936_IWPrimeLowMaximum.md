# Checkpoint 936: Actual prime low maximum with the selected Page character

The actual prime low operator used by the already checked high theorem now has its own full dyadic finite-input Lp majorant, with norm at most 2*K*D(r,k,Q) times the input norm. Lean identifies the operator exactly as the principal cyclic square term minus its selected fixed Page-character term, checks the actual induced character and its cyclic total variation, and uses the beta-uniform full IW low estimate for both. The varying activation mask is handled pointwise; it introduces no additional maximal hypothesis. Finite-input Lp membership is discharged by the norm bridge. No new external analytic input is introduced. The source review metadata now also records both exact active statement hashes. Actual low and high norms now refer to the same existing prime operators; their quantitative indicator distribution assembly and optimization are next.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| IWPrimeLowMaximum.lean | 4 |

- `iwPrimeLowOperator_none`
- `iwPrimeLowOperator_some`
- `iwPrimeLowOperator_some_norm`
- `iw_prime_finite_low_majorant`

<!-- checkpoint-verification -->

## Verification

All 1003 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4625-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2851 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1005 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed source results under their paper hypotheses remain unchanged. Lemma 3.21, both conclusions of Theorems 1.1 and 1.3, all displayed clauses of Proposition 4.19 and both clauses of Proposition 6.21 are complete checked implications under their separately recorded independent deep inputs. The square-sign reflection is proved. Theorem 1.3 has actual finite sparse families, disjoint major subsets and the literal full all-cutoff maximum. The three general Section5 auxiliary statements remain partial, and the later Orlicz/ergodic/sieve applications remain unfinished. Earlier Theorems1.1/1.3 and Propositions4.19/6.21 preserve their separately recorded raw prime/distribution, Page, generic smooth multifrequency, ordinary-square and stopping hypotheses. Section7 additionally records RawTaoArcConstructionInput C and RawIWMultiplierInput C as explicit unproved independent general theorems, not Lean axioms. Actual geometry and full goodness and conditional smooth multiplier specialization are proved. The actual prime high-side comparison uses raw Tao construction, SmoothCircleBourgainInput, RawPageUniquenessInput and PagePrimeSquareDistributionInputs; its own coefficient identities, cutoffs, Page selection and approximation deductions are proved. General sampling and concrete continuous/low estimates remain unfinished. The current-paper low maximum, restricted estimate and full high/low conclusion are not external input fields.

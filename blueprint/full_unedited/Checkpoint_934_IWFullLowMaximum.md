# Checkpoint 934: Full actual finite-input dyadic IW low maximum with D cost

The full actual dyadic IW low operator family on every finite complex input now has one nonnegative Lp majorant of norm at most K*D(r,k,Q) times the input norm. Lean assembles the exact short-scale maximum, the actual narrow countable maximum and the interpolated countable remainder, checks the exact dyadic reindexing and proves every cost fits D with K independent of the arithmetic parameters, beta, input and cyclic measure. All operator identities and applicability hypotheses are checked. Only the separately recorded independent general standard theorems are hypotheses; no own low/high/restricted estimate is assumed. The source ledger is reviewed without upgrading its partial claims: full printed all-input/real-Q clauses and the actual restricted maximal estimate remain unfinished.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| IWFullLowMaximum.lean | 5 |

- `iwCompleteLowConstant_pos`
- `iwMaximalCost_lower_bounds`
- `integer_operator_difference_bound`
- `iwAnnularLowOperator_scale_congr`
- `iw_finite_input_low_majorant`

<!-- checkpoint-verification -->

## Verification

All 1001 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4623-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2841 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1003 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed source results under their paper hypotheses remain unchanged. Lemma 3.21, both conclusions of Theorems 1.1 and 1.3, all displayed clauses of Proposition 4.19 and both clauses of Proposition 6.21 are complete checked implications under their separately recorded independent deep inputs. The square-sign reflection is proved. Theorem 1.3 has actual finite sparse families, disjoint major subsets and the literal full all-cutoff maximum. The three general Section5 auxiliary statements remain partial, and the later Orlicz/ergodic/sieve applications remain unfinished. Earlier Theorems1.1/1.3 and Propositions4.19/6.21 preserve their separately recorded raw prime/distribution, Page, generic smooth multifrequency, ordinary-square and stopping hypotheses. Section7 additionally records RawTaoArcConstructionInput C and RawIWMultiplierInput C as explicit unproved independent general theorems, not Lean axioms. Actual geometry and full goodness and conditional smooth multiplier specialization are proved. The actual prime high-side comparison uses raw Tao construction, SmoothCircleBourgainInput, RawPageUniquenessInput and PagePrimeSquareDistributionInputs; its own coefficient identities, cutoffs, Page selection and approximation deductions are proved. General sampling and concrete continuous/low estimates remain unfinished. The current-paper low maximum, restricted estimate and full high/low conclusion are not external input fields.

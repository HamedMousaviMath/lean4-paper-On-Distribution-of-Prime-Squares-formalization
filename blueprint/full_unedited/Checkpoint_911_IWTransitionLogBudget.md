# Checkpoint 911: Actual period width and integer transition-index logarithmic budgets

Lean proves the full source logarithmic budget for the actual transition index. The constructed period obeys log P<=2Q; the exact narrow width has -log(delta)<=100(Q+r log B); the natural ceiling index satisfies J_*+2<=101(Q+r log B); and log(2+J_*)<=101 log(e+Q+r log B). Every constant is absolute and every quantity is the actual source-defined one, with no extra parameter dependence. No analytic input or current-paper maximal estimate is assumed. Substitution into the actual finite low maximum is next.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| IWTransitionLogBudget.lean | 4 |

- `iw_period_log_bound`
- `iw_narrow_log_inverse_budget`
- `iw_transition_index_linear_budget`
- `iw_transition_log_cost_budget`

<!-- checkpoint-verification -->

## Verification

All 978 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4597-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2740 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 980 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed source results under their paper hypotheses remain unchanged. Lemma 3.21, both conclusions of Theorems 1.1 and 1.3, all displayed clauses of Proposition 4.19 and both clauses of Proposition 6.21 are complete checked implications under their separately recorded independent deep inputs. The square-sign reflection is proved. Theorem 1.3 has actual finite sparse families, disjoint major subsets and the literal full all-cutoff maximum. The three general Section5 auxiliary statements remain partial, and the later Orlicz/ergodic/sieve applications remain unfinished. Earlier Theorems1.1/1.3 and Propositions4.19/6.21 preserve their separately recorded raw prime/distribution, Page, generic smooth multifrequency, ordinary-square and stopping hypotheses. Section7 additionally records RawTaoArcConstructionInput C and RawIWMultiplierInput C as explicit unproved independent general theorems, not Lean axioms. Actual geometry and full goodness and conditional smooth multiplier specialization are proved. The actual prime high-side comparison uses raw Tao construction, SmoothCircleBourgainInput, RawPageUniquenessInput and PagePrimeSquareDistributionInputs; its own coefficient identities, cutoffs, Page selection and approximation deductions are proved. General sampling and concrete continuous/low estimates remain unfinished. The current-paper low maximum, restricted estimate and full high/low conclusion are not external input fields.

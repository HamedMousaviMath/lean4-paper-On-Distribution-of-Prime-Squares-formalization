# Checkpoint 965: Uniform logarithmic rate for the actual ordinary-square approximation

Lean proves a uniform source-scale bound for the actual ordinary annular Fourier approximation error: at every circle point the error is at most 4 Q^(-1/2) (1+log N)^(-2), for sufficiently large even N under log Q ≤ (1/8) sqrt(log N). The explicit major/minor and periodic model-tail budget is absorbed using proved logarithmic estimates. The geometric hypotheses are verified at the actual source radius, with the source parameter chosen to give the required cutoff range. This implication consumes only the declared independent scalar quadratic Weyl approximation for its arithmetic step; the paper-specific Fourier approximation is proved.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| FullSquareApproximationRate.lean | 5 |

- `fullSquareApproxBudget_log_bound`
- `eventually_fullSquareLogCost`
- `fullSquareLogCost_uniform`
- `sourceFullSquare_arc_conditions`
- `fullSquareCircleError_uniform`

<!-- checkpoint-verification -->

## Verification

All 1032 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4654-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2965 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1034 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed source results under their paper hypotheses remain unchanged. Lemma 3.21, both conclusions of Theorems 1.1 and 1.3, all displayed clauses of Proposition 4.19 and both clauses of Proposition 6.21 are complete checked implications under their separately recorded independent deep inputs. The square-sign reflection is proved. Theorem 1.3 has actual finite sparse families, disjoint major subsets and the literal full all-cutoff maximum. The three general Section5 auxiliary statements remain partial, and the later Orlicz/ergodic/sieve applications remain unfinished. Earlier Theorems1.1/1.3 and Propositions4.19/6.21 preserve their separately recorded raw prime/distribution, Page, generic smooth multifrequency, ordinary-square and stopping hypotheses. Section7 additionally records RawTaoArcConstructionInput C and RawIWMultiplierInput C as explicit unproved independent general theorems, not Lean axioms. Actual geometry and full goodness and conditional smooth multiplier specialization are proved. The actual prime high-side comparison uses raw Tao construction, SmoothCircleBourgainInput, RawPageUniquenessInput and PagePrimeSquareDistributionInputs; its own coefficient identities, cutoffs, Page selection and approximation deductions are proved. General sampling and concrete continuous/low estimates remain unfinished. The current-paper low maximum, restricted estimate and full high/low conclusion are not external input fields.

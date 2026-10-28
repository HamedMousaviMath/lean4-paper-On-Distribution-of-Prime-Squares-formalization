# Checkpoint 912: Actual short-scale IW low maximum with the precise D(r,k,Q) cost

Lean proves the actual short-scale IW low maximum for every dyadic N<=N_* has the paper's precise K*D(r,k,Q) bound, uniformly in beta, the cyclic complex measure and the arithmetic parameters. This uses the actual natural-ceiling transition index, period P<=3^Q, exact original/narrow widths, the checked r*C_(r,k)*log(2+J) finite cost and C_(r,k)>=1. Membership and extended-norm control are explicit. K depends only on the fixed cutoff and the recorded general standard analytic constants. No own-paper low maximum is assumed. The narrow large-scale maximum, summed cutoff remainder and actual restricted estimate remain unfinished; source Proposition7.22 stays partial.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| IWShortTransitionMaximum.lean | 3 |

- `iwFiniteLowConstant_nonneg`
- `iw_short_transition_cost_bound`
- `iw_short_transition_maximum`

<!-- checkpoint-verification -->

## Verification

All 979 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4598-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2743 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 981 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed source results under their paper hypotheses remain unchanged. Lemma 3.21, both conclusions of Theorems 1.1 and 1.3, all displayed clauses of Proposition 4.19 and both clauses of Proposition 6.21 are complete checked implications under their separately recorded independent deep inputs. The square-sign reflection is proved. Theorem 1.3 has actual finite sparse families, disjoint major subsets and the literal full all-cutoff maximum. The three general Section5 auxiliary statements remain partial, and the later Orlicz/ergodic/sieve applications remain unfinished. Earlier Theorems1.1/1.3 and Propositions4.19/6.21 preserve their separately recorded raw prime/distribution, Page, generic smooth multifrequency, ordinary-square and stopping hypotheses. Section7 additionally records RawTaoArcConstructionInput C and RawIWMultiplierInput C as explicit unproved independent general theorems, not Lean axioms. Actual geometry and full goodness and conditional smooth multiplier specialization are proved. The actual prime high-side comparison uses raw Tao construction, SmoothCircleBourgainInput, RawPageUniquenessInput and PagePrimeSquareDistributionInputs; its own coefficient identities, cutoffs, Page selection and approximation deductions are proved. General sampling and concrete continuous/low estimates remain unfinished. The current-paper low maximum, restricted estimate and full high/low conclusion are not external input fields.

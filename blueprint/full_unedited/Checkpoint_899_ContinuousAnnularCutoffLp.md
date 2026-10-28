# Checkpoint 899: Actual signed cutoff Lp bounds with a single near-one loss and initial-scale control

Lean proves the actual signed cutoff symbol factors exactly into the uncut signed symbol and source cutoff. Operator composition combines the checked continuous singular-integral implication with the invariant-L1 Young cutoff bound, retaining precisely one factor 1/(p-1), not an extra near-one loss. The actual annular kernel has integral norm at most 1 for every N>=1 and 0<beta<=1; Young therefore also supplies the actual individual annular and cutoff bounds, including N=1. No current-paper low maximum or restricted estimate is a premise. Independent general Hormander and Young theorem parameters remain explicit.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| ContinuousAnnularCutoffLp.lean | 7 |

- `continuousAnnularSignedSymbol_cutoff`
- `continuousAnnularCutoffSignedMultiplier_Lp`
- `allAnnularBoundedSymbol_untruncated`
- `continuousAnnularKernel_integral_norm_le`
- `annularYoungMultiplier_Lp`
- `allAnnularBoundedSymbol_cutoff`
- `annularCutoffYoungMultiplier_Lp`

<!-- checkpoint-verification -->

## Verification

All 966 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4585-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2699 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 968 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed source results under their paper hypotheses remain unchanged. Lemma 3.21, both conclusions of Theorems 1.1 and 1.3, all displayed clauses of Proposition 4.19 and both clauses of Proposition 6.21 are complete checked implications under their separately recorded independent deep inputs. The square-sign reflection is proved. Theorem 1.3 has actual finite sparse families, disjoint major subsets and the literal full all-cutoff maximum. The three general Section5 auxiliary statements remain partial, and the later Orlicz/ergodic/sieve applications remain unfinished. Earlier Theorems1.1/1.3 and Propositions4.19/6.21 preserve their separately recorded raw prime/distribution, Page, generic smooth multifrequency, ordinary-square and stopping hypotheses. Section7 additionally records RawTaoArcConstructionInput C and RawIWMultiplierInput C as explicit unproved independent general theorems, not Lean axioms. Actual geometry and full goodness and conditional smooth multiplier specialization are proved. The actual prime high-side comparison uses raw Tao construction, SmoothCircleBourgainInput, RawPageUniquenessInput and PagePrimeSquareDistributionInputs; its own coefficient identities, cutoffs, Page selection and approximation deductions are proved. General sampling and concrete continuous/low estimates remain unfinished. The current-paper low maximum, restricted estimate and full high/low conclusion are not external input fields.

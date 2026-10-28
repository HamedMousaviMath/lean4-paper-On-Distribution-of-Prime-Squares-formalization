# Checkpoint 905: Actual finite IW increment maximum with logarithmic scale-count dependence

Lean applies the general finite signed-sum maximal theorem to the literal increments of the actual IW annular low operators. It proves the exact coordinate identity between the signed scalar sequence and the signed operator, supplies the already checked K*r*C_(r,k) bound for every complex sign choice, and derives the actual partial-sum maximum with logarithmic cost log(2+J), membership and extended-norm control. Only explicitly recorded general standard analytic inputs are used; no paper-specific maximum is an input. Adding the separately checked initial annular term to obtain the actual finite low maximum is next.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| IWShortScaleIncrementMaximum.lean | 2 |

- `iwAnnularIncrementSequence_signed`
- `iw_short_scale_increment_maximum`

<!-- checkpoint-verification -->

## Verification

All 972 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4591-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2720 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 974 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed source results under their paper hypotheses remain unchanged. Lemma 3.21, both conclusions of Theorems 1.1 and 1.3, all displayed clauses of Proposition 4.19 and both clauses of Proposition 6.21 are complete checked implications under their separately recorded independent deep inputs. The square-sign reflection is proved. Theorem 1.3 has actual finite sparse families, disjoint major subsets and the literal full all-cutoff maximum. The three general Section5 auxiliary statements remain partial, and the later Orlicz/ergodic/sieve applications remain unfinished. Earlier Theorems1.1/1.3 and Propositions4.19/6.21 preserve their separately recorded raw prime/distribution, Page, generic smooth multifrequency, ordinary-square and stopping hypotheses. Section7 additionally records RawTaoArcConstructionInput C and RawIWMultiplierInput C as explicit unproved independent general theorems, not Lean axioms. Actual geometry and full goodness and conditional smooth multiplier specialization are proved. The actual prime high-side comparison uses raw Tao construction, SmoothCircleBourgainInput, RawPageUniquenessInput and PagePrimeSquareDistributionInputs; its own coefficient identities, cutoffs, Page selection and approximation deductions are proved. General sampling and concrete continuous/low estimates remain unfinished. The current-paper low maximum, restricted estimate and full high/low conclusion are not external input fields.

# Checkpoint 877: Continuous signed increments including the initial N-equals-one scale

The continuous signed-increment multiplier estimate now includes the actual N=1 starting term in the manuscript. Lean proves the uniform annular symbol bound at every N>=1, including the beta-uniform edge case, and combines the first increment with the checked later-scale sum. The resulting constant is independent of beta, frequency, length and complex signs. This completes the scalar multiplier preparation for a genuine Plancherel L2 operator bound; no general-p continuous or maximal theorem is assumed.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| ContinuousAnnularInitialIncrement.lean | 3 |

- `annularOscillatoryModel_norm_one`
- `continuousAnnularIncrement_one_start`
- `continuousAnnularSignedIncrement_one_start`

<!-- checkpoint-verification -->

## Verification

All 944 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4563-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2618 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 946 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed source results under their paper hypotheses remain unchanged. Lemma 3.21, both conclusions of Theorems 1.1 and 1.3, all displayed clauses of Proposition 4.19 and both clauses of Proposition 6.21 are complete checked implications under their separately recorded independent deep inputs. The square-sign reflection is proved. Theorem 1.3 has actual finite sparse families, disjoint major subsets and the literal full all-cutoff maximum. The three general Section5 auxiliary statements remain partial, and the later Orlicz/ergodic/sieve applications remain unfinished. Earlier Theorems1.1/1.3 and Propositions4.19/6.21 preserve their separately recorded raw prime/distribution, Page, generic smooth multifrequency, ordinary-square and stopping hypotheses. Section7 additionally records RawTaoArcConstructionInput C and RawIWMultiplierInput C as explicit unproved independent general theorems, not Lean axioms. Actual geometry and full goodness and conditional smooth multiplier specialization are proved. The actual prime high-side comparison uses raw Tao construction, SmoothCircleBourgainInput, RawPageUniquenessInput and PagePrimeSquareDistributionInputs; its own coefficient identities, cutoffs, Page selection and approximation deductions are proved. General sampling and concrete continuous/low estimates remain unfinished. The current-paper low maximum, restricted estimate and full high/low conclusion are not external input fields.

# Checkpoint 906: Checked telescoping and Lp assembly of a finite family maximum from its increments

Lean proves a general finite-family maximal assembly from consecutive differences: exact telescoping, pointwise domination by the initial norm plus the partial-sum maximum, and the actual Lp membership and extended-norm triangle bound. This applies to arbitrary L2-valued sequences on the integers and uses only already formalized algebra, finite suprema and Lp inequalities. It introduces no independent analytic input. Combining it with the checked actual IW initial and increment bounds will yield the finite low-family maximum.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| FiniteDifferenceMaximum.lean | 3 |

- `finiteDifferenceSequence_telescope`
- `finiteDifferenceSequence_maximum_bound`
- `finiteDifferenceSequence_maximum_Lp`

<!-- checkpoint-verification -->

## Verification

All 973 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4592-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2723 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 975 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed source results under their paper hypotheses remain unchanged. Lemma 3.21, both conclusions of Theorems 1.1 and 1.3, all displayed clauses of Proposition 4.19 and both clauses of Proposition 6.21 are complete checked implications under their separately recorded independent deep inputs. The square-sign reflection is proved. Theorem 1.3 has actual finite sparse families, disjoint major subsets and the literal full all-cutoff maximum. The three general Section5 auxiliary statements remain partial, and the later Orlicz/ergodic/sieve applications remain unfinished. Earlier Theorems1.1/1.3 and Propositions4.19/6.21 preserve their separately recorded raw prime/distribution, Page, generic smooth multifrequency, ordinary-square and stopping hypotheses. Section7 additionally records RawTaoArcConstructionInput C and RawIWMultiplierInput C as explicit unproved independent general theorems, not Lean axioms. Actual geometry and full goodness and conditional smooth multiplier specialization are proved. The actual prime high-side comparison uses raw Tao construction, SmoothCircleBourgainInput, RawPageUniquenessInput and PagePrimeSquareDistributionInputs; its own coefficient identities, cutoffs, Page selection and approximation deductions are proved. General sampling and concrete continuous/low estimates remain unfinished. The current-paper low maximum, restricted estimate and full high/low conclusion are not external input fields.

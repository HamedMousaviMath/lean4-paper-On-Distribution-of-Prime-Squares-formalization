# Checkpoint 928: Actual narrow annular finite maximum on real and normalized cyclic Schwartz families

For arbitrary Schwartz inputs, Lean proves the literal finite maximum of the actual annular narrow-cutoff Schwartz outputs belongs to Lp and has norm at most (H/(p-1))*cutoffL1Constant times the input norm, uniformly over arbitrary finite collections of integer scales at least two and 0<=beta<=1. Its realization as the actual continuous annular convolution, finite maximum measurability, common Hardy-Littlewood majorant and Young cutoff cost are all checked. The estimate lifts to arbitrary normalized cyclic Schwartz families without any dependence on the number of scales or the period. Only the recorded independent general Hardy-Littlewood and Young inputs are used. The final narrow sampling and full low maximum assembly are next.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| SchwartzAnnularMaximum.lean | 4 |

- `annularSchwartzOutput_convolution`
- `cutoffSchwartzOutput_Lp`
- `annularSchwartzOutput_maximum_Lp`
- `cyclic_annularSchwartzOutput_maximum`

<!-- checkpoint-verification -->

## Verification

All 995 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4616-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2822 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 997 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed source results under their paper hypotheses remain unchanged. Lemma 3.21, both conclusions of Theorems 1.1 and 1.3, all displayed clauses of Proposition 4.19 and both clauses of Proposition 6.21 are complete checked implications under their separately recorded independent deep inputs. The square-sign reflection is proved. Theorem 1.3 has actual finite sparse families, disjoint major subsets and the literal full all-cutoff maximum. The three general Section5 auxiliary statements remain partial, and the later Orlicz/ergodic/sieve applications remain unfinished. Earlier Theorems1.1/1.3 and Propositions4.19/6.21 preserve their separately recorded raw prime/distribution, Page, generic smooth multifrequency, ordinary-square and stopping hypotheses. Section7 additionally records RawTaoArcConstructionInput C and RawIWMultiplierInput C as explicit unproved independent general theorems, not Lean axioms. Actual geometry and full goodness and conditional smooth multiplier specialization are proved. The actual prime high-side comparison uses raw Tao construction, SmoothCircleBourgainInput, RawPageUniquenessInput and PagePrimeSquareDistributionInputs; its own coefficient identities, cutoffs, Page selection and approximation deductions are proved. General sampling and concrete continuous/low estimates remain unfinished. The current-paper low maximum, restricted estimate and full high/low conclusion are not external input fields.

# Checkpoint 872: Uniform annular mass variation and reviewed prime high-side milestone

Lean now proves the exact zero-frequency mass factor for the actual annular model, its uniform bound by one, positivity and monotonicity in the scale, and uniform total variation at most one along every finite dyadic range. These are beta-uniform proved ingredients for the continuous signed-increment argument; the complete continuous Lp lemma is not claimed. This checkpoint also reviews the exact source statements against the checked prime high theorem at871: p:orlicz-hilo moves from open to partial only. The actual restricted estimate, low maximum and ordinary-square companion remain unproved. Documentation and recovery metadata are reconciled with the new scope and 54-claim inventory.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| AnnularMassVariation.lean | 7 |

- `annularMassFactor_nonneg`
- `annularMassFactor_le_one`
- `annularMass_formula`
- `annularMass_re_bounds`
- `annularMass_re_antitone`
- `annularMass_difference_norm`
- `annularMass_dyadic_variation`

<!-- checkpoint-verification -->

## Verification

All 939 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4558-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2595 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 941 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed source results under their paper hypotheses remain unchanged. Lemma 3.21, both conclusions of Theorems 1.1 and 1.3, all displayed clauses of Proposition 4.19 and both clauses of Proposition 6.21 are complete checked implications under their separately recorded independent deep inputs. The square-sign reflection is proved. Theorem 1.3 has actual finite sparse families, disjoint major subsets and the literal full all-cutoff maximum. The three general Section5 auxiliary statements remain partial, and the later Orlicz/ergodic/sieve applications remain unfinished. Earlier Theorems1.1/1.3 and Propositions4.19/6.21 preserve their separately recorded raw prime/distribution, Page, generic smooth multifrequency, ordinary-square and stopping hypotheses. Section7 additionally records RawTaoArcConstructionInput C and RawIWMultiplierInput C as explicit unproved independent general theorems, not Lean axioms. Actual geometry and full goodness and conditional smooth multiplier specialization are proved. The actual prime high-side comparison uses raw Tao construction, SmoothCircleBourgainInput, RawPageUniquenessInput and PagePrimeSquareDistributionInputs; its own coefficient identities, cutoffs, Page selection and approximation deductions are proved. General sampling and concrete continuous/low estimates remain unfinished. The current-paper low maximum, restricted estimate and full high/low conclusion are not external input fields.

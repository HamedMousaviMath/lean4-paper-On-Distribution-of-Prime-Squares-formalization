# Checkpoint 959: The full quadratic oscillatory integral bound is proved

Lean proves the full initial-interval quadratic oscillatory integral bound by splitting at |theta|^(-1/2), using unit modulus on the initial segment and the proved integration-by-parts tail afterward. The exact constant is 1+3/(4*pi). The actual normalized initial continuous square model has norm at most one and the required 1/(N*sqrt(|theta|)) decay. These estimates are proved from Mathlib calculus, with no independent Fresnel or continuous-decay hypothesis.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| QuadraticIntegralBound.lean | 5 |

- `quadraticIntegralConstant_one_le`
- `quadratic_integral_norm_le_length`
- `quadratic_integral_uniform_bound`
- `initialQuadraticModel_norm_one`
- `initialQuadraticModel_decay`

<!-- checkpoint-verification -->

## Verification

All 1026 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4648-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2940 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1028 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed source results under their paper hypotheses remain unchanged. Lemma 3.21, both conclusions of Theorems 1.1 and 1.3, all displayed clauses of Proposition 4.19 and both clauses of Proposition 6.21 are complete checked implications under their separately recorded independent deep inputs. The square-sign reflection is proved. Theorem 1.3 has actual finite sparse families, disjoint major subsets and the literal full all-cutoff maximum. The three general Section5 auxiliary statements remain partial, and the later Orlicz/ergodic/sieve applications remain unfinished. Earlier Theorems1.1/1.3 and Propositions4.19/6.21 preserve their separately recorded raw prime/distribution, Page, generic smooth multifrequency, ordinary-square and stopping hypotheses. Section7 additionally records RawTaoArcConstructionInput C and RawIWMultiplierInput C as explicit unproved independent general theorems, not Lean axioms. Actual geometry and full goodness and conditional smooth multiplier specialization are proved. The actual prime high-side comparison uses raw Tao construction, SmoothCircleBourgainInput, RawPageUniquenessInput and PagePrimeSquareDistributionInputs; its own coefficient identities, cutoffs, Page selection and approximation deductions are proved. General sampling and concrete continuous/low estimates remain unfinished. The current-paper low maximum, restricted estimate and full high/low conclusion are not external input fields.

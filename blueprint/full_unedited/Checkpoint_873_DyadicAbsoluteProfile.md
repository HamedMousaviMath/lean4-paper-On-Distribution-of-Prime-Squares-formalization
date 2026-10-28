# Checkpoint 873: Uniform absolute dyadic profile sum for the continuous increment argument

Lean now proves a uniform absolute geometric profile sum: sum over j<J of min(4^j*x,(4^j*x)^(-1))<=10/3 for every nonnegative x, including zero. A positive rational potential gives exact telescoping and avoids any unverified cutoff at a logarithmic index. The companion two-sided profile lemma converts the already proved annular small- and large-frequency estimates into this summable form. These are proved scalar ingredients for the continuous signed-increment estimate; no low maximal conclusion is assumed.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| DyadicAbsoluteProfile.lean | 8 |

- `absoluteDyadicPotential_range`
- `absoluteDyadicPotential_difference`
- `absoluteDyadicPotential_near`
- `absoluteDyadicPotential_far`
- `absoluteDyadicProfile_bound`
- `two_sided_absolute_profile`
- `absoluteDyadicPotential_telescoping`
- `dyadic_absolute_profile_sum`

<!-- checkpoint-verification -->

## Verification

All 940 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4559-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2603 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 942 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed source results under their paper hypotheses remain unchanged. Lemma 3.21, both conclusions of Theorems 1.1 and 1.3, all displayed clauses of Proposition 4.19 and both clauses of Proposition 6.21 are complete checked implications under their separately recorded independent deep inputs. The square-sign reflection is proved. Theorem 1.3 has actual finite sparse families, disjoint major subsets and the literal full all-cutoff maximum. The three general Section5 auxiliary statements remain partial, and the later Orlicz/ergodic/sieve applications remain unfinished. Earlier Theorems1.1/1.3 and Propositions4.19/6.21 preserve their separately recorded raw prime/distribution, Page, generic smooth multifrequency, ordinary-square and stopping hypotheses. Section7 additionally records RawTaoArcConstructionInput C and RawIWMultiplierInput C as explicit unproved independent general theorems, not Lean axioms. Actual geometry and full goodness and conditional smooth multiplier specialization are proved. The actual prime high-side comparison uses raw Tao construction, SmoothCircleBourgainInput, RawPageUniquenessInput and PagePrimeSquareDistributionInputs; its own coefficient identities, cutoffs, Page selection and approximation deductions are proved. General sampling and concrete continuous/low estimates remain unfinished. The current-paper low maximum, restricted estimate and full high/low conclusion are not external input fields.

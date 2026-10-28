# Checkpoint 901: Actual IW signed annular multiplier bound with explicit r times C_(r,k) dependence

Lean transfers the actual bounded smooth signed annular cutoff symbol through the corrected general IW multiplier theorem at p_r=(2r)'. It proves the exact narrow-support applicability, C-infinity applicability, positivity and near-one arithmetic, yielding the quantitative actual integer Lp bound K*r*C_(r,k), with K depending only on the recorded general scalar Hormander constant and the fixed cutoff L1 norm. The estimate is uniform in Q, the finite cyclic measure of variation at most one, beta, the number of increments and arbitrary complex signs. All output membership is explicit. Only the already recorded general IW, Hormander and Young parameters are used; no current-paper low maximum or restricted result is a premise. The exact signed-family identity and finite maximal deduction are next.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| IWSignedAnnularBounds.lean | 7 |

- `scaled_cutoff_boundary_zero`
- `allAnnularBoundedSymbol_boundary`
- `continuousAnnularSignedSymbol_boundary`
- `iwNearOneExponent_cost`
- `iwMultiplierConstant_nonneg`
- `iwAnnularIncrementCost_nonneg`
- `iw_signed_annular_multiplier`

<!-- checkpoint-verification -->

## Verification

All 968 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4587-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2710 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 970 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed source results under their paper hypotheses remain unchanged. Lemma 3.21, both conclusions of Theorems 1.1 and 1.3, all displayed clauses of Proposition 4.19 and both clauses of Proposition 6.21 are complete checked implications under their separately recorded independent deep inputs. The square-sign reflection is proved. Theorem 1.3 has actual finite sparse families, disjoint major subsets and the literal full all-cutoff maximum. The three general Section5 auxiliary statements remain partial, and the later Orlicz/ergodic/sieve applications remain unfinished. Earlier Theorems1.1/1.3 and Propositions4.19/6.21 preserve their separately recorded raw prime/distribution, Page, generic smooth multifrequency, ordinary-square and stopping hypotheses. Section7 additionally records RawTaoArcConstructionInput C and RawIWMultiplierInput C as explicit unproved independent general theorems, not Lean axioms. Actual geometry and full goodness and conditional smooth multiplier specialization are proved. The actual prime high-side comparison uses raw Tao construction, SmoothCircleBourgainInput, RawPageUniquenessInput and PagePrimeSquareDistributionInputs; its own coefficient identities, cutoffs, Page selection and approximation deductions are proved. General sampling and concrete continuous/low estimates remain unfinished. The current-paper low maximum, restricted estimate and full high/low conclusion are not external input fields.

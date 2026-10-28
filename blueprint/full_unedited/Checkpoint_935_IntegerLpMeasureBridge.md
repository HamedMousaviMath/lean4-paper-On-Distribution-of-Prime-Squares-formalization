# Checkpoint 935: Exact integer Lp norm bridge and indicator power budget

Lean proves the exact bridge between counting-measure Lp functions and the existing integer lp sequences at every positive finite exponent, including equality of the extended measure norm with the integer sequence norm. Finite complex inputs are thereby proved to satisfy every Lp membership hypothesis used by the actual low theorem. The exact indicator norm power is checked, and an actual Lp majorant bounded by K times the indicator input norm is converted into the finite power budget K^p*|F| required by the restricted-distribution argument. These are proved norm and membership identities, not additional independent inputs.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| IntegerLpMeasureBridge.lean | 6 |

- `memℓp_of_count_memLp`
- `eLpNorm_count_eq_lp_enorm`
- `count_memLp_of_memℓp`
- `finiteInputLp_count_memLp`
- `finiteIndicatorLp_norm_power`
- `count_Lp_indicator_power_budget`

<!-- checkpoint-verification -->

## Verification

All 1002 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4624-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2847 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1004 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed source results under their paper hypotheses remain unchanged. Lemma 3.21, both conclusions of Theorems 1.1 and 1.3, all displayed clauses of Proposition 4.19 and both clauses of Proposition 6.21 are complete checked implications under their separately recorded independent deep inputs. The square-sign reflection is proved. Theorem 1.3 has actual finite sparse families, disjoint major subsets and the literal full all-cutoff maximum. The three general Section5 auxiliary statements remain partial, and the later Orlicz/ergodic/sieve applications remain unfinished. Earlier Theorems1.1/1.3 and Propositions4.19/6.21 preserve their separately recorded raw prime/distribution, Page, generic smooth multifrequency, ordinary-square and stopping hypotheses. Section7 additionally records RawTaoArcConstructionInput C and RawIWMultiplierInput C as explicit unproved independent general theorems, not Lean axioms. Actual geometry and full goodness and conditional smooth multiplier specialization are proved. The actual prime high-side comparison uses raw Tao construction, SmoothCircleBourgainInput, RawPageUniquenessInput and PagePrimeSquareDistributionInputs; its own coefficient identities, cutoffs, Page selection and approximation deductions are proved. General sampling and concrete continuous/low estimates remain unfinished. The current-paper low maximum, restricted estimate and full high/low conclusion are not external input fields.

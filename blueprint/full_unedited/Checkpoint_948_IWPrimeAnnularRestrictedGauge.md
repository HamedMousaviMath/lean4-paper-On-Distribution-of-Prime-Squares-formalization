# Checkpoint 948: Actual prime annular restricted Orlicz estimate from the quantitative IW comparison

The actual dyadic annular von Mangoldt square maximal operator now satisfies the claimed restricted near-one Orlicz estimate for every finite indicator and every t>=1. Lean proves existence of nonnegative Cg and positive Rg and proves PositiveRestrictedGauge for the actual arithmetic family. It instantiates the concrete checked low/high distribution inequality at the checked integer parameters and starting index, applies the complete scalar budget and compares t*exp(Cg sqrt(log(e+t) log(e+log(e+t)))) with the integral gauge Psi. The paper-specific restricted estimate is a conclusion, not an independent hypothesis. The general IW, sampling, continuous, interpolation, Page and distribution inputs retain their explicit boundaries. The all-integer cutoff transfer and unweighted normalization are separate assemblies.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| IWPrimeAnnularRestrictedGauge.lean | 1 |

- `iw_prime_annular_restricted_gauge`

<!-- checkpoint-verification -->

## Verification

All 1015 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4637-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2894 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1017 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed source results under their paper hypotheses remain unchanged. Lemma 3.21, both conclusions of Theorems 1.1 and 1.3, all displayed clauses of Proposition 4.19 and both clauses of Proposition 6.21 are complete checked implications under their separately recorded independent deep inputs. The square-sign reflection is proved. Theorem 1.3 has actual finite sparse families, disjoint major subsets and the literal full all-cutoff maximum. The three general Section5 auxiliary statements remain partial, and the later Orlicz/ergodic/sieve applications remain unfinished. Earlier Theorems1.1/1.3 and Propositions4.19/6.21 preserve their separately recorded raw prime/distribution, Page, generic smooth multifrequency, ordinary-square and stopping hypotheses. Section7 additionally records RawTaoArcConstructionInput C and RawIWMultiplierInput C as explicit unproved independent general theorems, not Lean axioms. Actual geometry and full goodness and conditional smooth multiplier specialization are proved. The actual prime high-side comparison uses raw Tao construction, SmoothCircleBourgainInput, RawPageUniquenessInput and PagePrimeSquareDistributionInputs; its own coefficient identities, cutoffs, Page selection and approximation deductions are proved. General sampling and concrete continuous/low estimates remain unfinished. The current-paper low maximum, restricted estimate and full high/low conclusion are not external input fields.

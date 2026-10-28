# Checkpoint 924: Concrete smooth finite-input Fourier lift and actual IW projection formula

Lean constructs the concrete compact smooth Fourier amplitudes for every finite complex integer input and arbitrary smooth compact real symbol, and their actual inverse Schwartz transforms. Their Fourier transforms, support boundary, smoothness, periodization and rational-shift identities are checked. The existing integer IW multiplier on the finite input is exactly the finite sum of these modulated real lift components with the actual cyclic Fourier coefficients. This establishes the Fourier algebra needed for sampling, rather than assuming an intertwining identity. The cyclic residue diagonal identification, lift norm bound and narrow main-term maximum remain next.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| FiniteSmoothFourierLift.lean | 11 |

- `compact_support_of_unit_boundary`
- `finiteFourierPolynomial_shift_smooth`
- `finiteLiftFrequencyMap_boundary`
- `finiteLiftFrequencyMap_smooth`
- `finiteLiftFrequencySchwartz_apply`
- `finiteLiftComponent_fourier`
- `finiteLiftFrequency_periodization`
- `finiteLiftFrequency_shift_periodization`
- `finiteLiftComponent_inverse`
- `finite_arc_projection_formula`
- `iwCyclicSymbol_finite_lift`

<!-- checkpoint-verification -->

## Verification

All 991 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4611-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2796 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 993 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed source results under their paper hypotheses remain unchanged. Lemma 3.21, both conclusions of Theorems 1.1 and 1.3, all displayed clauses of Proposition 4.19 and both clauses of Proposition 6.21 are complete checked implications under their separately recorded independent deep inputs. The square-sign reflection is proved. Theorem 1.3 has actual finite sparse families, disjoint major subsets and the literal full all-cutoff maximum. The three general Section5 auxiliary statements remain partial, and the later Orlicz/ergodic/sieve applications remain unfinished. Earlier Theorems1.1/1.3 and Propositions4.19/6.21 preserve their separately recorded raw prime/distribution, Page, generic smooth multifrequency, ordinary-square and stopping hypotheses. Section7 additionally records RawTaoArcConstructionInput C and RawIWMultiplierInput C as explicit unproved independent general theorems, not Lean axioms. Actual geometry and full goodness and conditional smooth multiplier specialization are proved. The actual prime high-side comparison uses raw Tao construction, SmoothCircleBourgainInput, RawPageUniquenessInput and PagePrimeSquareDistributionInputs; its own coefficient identities, cutoffs, Page selection and approximation deductions are proved. General sampling and concrete continuous/low estimates remain unfinished. The current-paper low maximum, restricted estimate and full high/low conclusion are not external input fields.

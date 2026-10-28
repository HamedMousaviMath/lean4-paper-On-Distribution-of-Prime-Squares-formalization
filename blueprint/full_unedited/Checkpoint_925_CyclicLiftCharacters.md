# Checkpoint 925: Actual cyclic diagonal identification and quantitative finite-input lift bound

Lean proves the exact rational-character descent from integers to the finite cyclic group, including subtraction and the actual residue-valued diagonal. Cyclic convolution of the synthesis is identified with multiplication by the literal cyclic Fourier coefficients. The point mass has total variation and Fourier coefficients exactly one. Consequently the actual diagonal of the constructed finite-input lift is precisely the existing IW cutoff projection, and its cyclic convolution has the actual weighted IW projection as diagonal. Combining these identities with the separately recorded independent major-arc sampling and IW multiplier hypotheses gives the lift norm bound Crk^2*K times the finite-input norm. No intertwining or own low maximum is assumed. The narrow annular real-variable maximum and Shannon application remain unfinished.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| CyclicLiftCharacters.lean | 10 |

- `rationalCharacter_eq_of_cyclic_cast`
- `cyclicLiftCharacter_integer`
- `cyclicLiftCharacter_sub`
- `cyclicSynthesis_convolution`
- `cyclicSynthesis_diagonal`
- `cyclicPointMass_variation`
- `cyclicPointMass_coefficient`
- `iw_finite_lift_diagonal`
- `iw_cyclic_convolution_lift_diagonal`
- `iw_finite_lift_size`

<!-- checkpoint-verification -->

## Verification

All 992 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4612-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2806 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 994 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed source results under their paper hypotheses remain unchanged. Lemma 3.21, both conclusions of Theorems 1.1 and 1.3, all displayed clauses of Proposition 4.19 and both clauses of Proposition 6.21 are complete checked implications under their separately recorded independent deep inputs. The square-sign reflection is proved. Theorem 1.3 has actual finite sparse families, disjoint major subsets and the literal full all-cutoff maximum. The three general Section5 auxiliary statements remain partial, and the later Orlicz/ergodic/sieve applications remain unfinished. Earlier Theorems1.1/1.3 and Propositions4.19/6.21 preserve their separately recorded raw prime/distribution, Page, generic smooth multifrequency, ordinary-square and stopping hypotheses. Section7 additionally records RawTaoArcConstructionInput C and RawIWMultiplierInput C as explicit unproved independent general theorems, not Lean axioms. Actual geometry and full goodness and conditional smooth multiplier specialization are proved. The actual prime high-side comparison uses raw Tao construction, SmoothCircleBourgainInput, RawPageUniquenessInput and PagePrimeSquareDistributionInputs; its own coefficient identities, cutoffs, Page selection and approximation deductions are proved. General sampling and concrete continuous/low estimates remain unfinished. The current-paper low maximum, restricted estimate and full high/low conclusion are not external input fields.

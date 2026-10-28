# Checkpoint 900: Exact subtraction and finite-combination identities for actual IW symbols

Lean proves exact linearity of the literal compact periodization and actual cyclic IW symbols under subtraction and arbitrary finite complex linear combinations. The support hypotheses are explicit for every source and target symbol. The proof works directly with the periodization window and the actual rational-frequency sum, retaining all cyclic Fourier coefficients. No norm inequality or independent analytic input is introduced. This supplies the exact identification between the forthcoming transferred signed multiplier and signed differences of the actual IW annular low family.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| IWSymbolLinearity.lean | 4 |

- `compactCircleLift_bounded_sub`
- `compactCircleLift_bounded_combination`
- `iwCyclicSymbol_sub`
- `iwCyclicSymbol_combination`

<!-- checkpoint-verification -->

## Verification

All 967 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4586-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2703 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 969 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed source results under their paper hypotheses remain unchanged. Lemma 3.21, both conclusions of Theorems 1.1 and 1.3, all displayed clauses of Proposition 4.19 and both clauses of Proposition 6.21 are complete checked implications under their separately recorded independent deep inputs. The square-sign reflection is proved. Theorem 1.3 has actual finite sparse families, disjoint major subsets and the literal full all-cutoff maximum. The three general Section5 auxiliary statements remain partial, and the later Orlicz/ergodic/sieve applications remain unfinished. Earlier Theorems1.1/1.3 and Propositions4.19/6.21 preserve their separately recorded raw prime/distribution, Page, generic smooth multifrequency, ordinary-square and stopping hypotheses. Section7 additionally records RawTaoArcConstructionInput C and RawIWMultiplierInput C as explicit unproved independent general theorems, not Lean axioms. Actual geometry and full goodness and conditional smooth multiplier specialization are proved. The actual prime high-side comparison uses raw Tao construction, SmoothCircleBourgainInput, RawPageUniquenessInput and PagePrimeSquareDistributionInputs; its own coefficient identities, cutoffs, Page selection and approximation deductions are proved. General sampling and concrete continuous/low estimates remain unfinished. The current-paper low maximum, restricted estimate and full high/low conclusion are not external input fields.

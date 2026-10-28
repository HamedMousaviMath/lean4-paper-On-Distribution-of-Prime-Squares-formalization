# Checkpoint 954: The actual cyclic square measure for all integer residues

Lean defines the actual cyclic probability measure obtained by squaring every residue, including nonunits, with group-order normalization. Its test-function formula, total variation at most one, exact complete quadratic Gauss Fourier coefficient and norm-at-most-one bound are proved. This is the distinct measure needed for ordinary integer squares; the earlier unit-residue prime measure is unchanged. Workspace maintenance removed the compiler and dependency caches, so the exact pinned environment was restored and all 1020 recovered project modules plus the root were freshly compiled. All recovered Lean hashes agree with checkpoint953. The original compilation receipt is preserved, the process-path compatibility shim affects no Lean compiler/kernel code, and the new baseline and fresh complete audits are recorded. No ordinary restricted estimate or complete Theorem7.2 is claimed at this stage.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| CyclicFullSquareMeasures.lean | 4 |

- `cyclicFullSquareMeasure_test`
- `cyclicFullSquareMeasure_variation_le_one`
- `cyclicFullSquareMeasure_fourier`
- `cyclicFullSquareMeasure_fourier_norm_le_one`

<!-- checkpoint-verification -->

## Verification

All 1021 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4643-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2915 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1023 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed source results under their paper hypotheses remain unchanged. Lemma 3.21, both conclusions of Theorems 1.1 and 1.3, all displayed clauses of Proposition 4.19 and both clauses of Proposition 6.21 are complete checked implications under their separately recorded independent deep inputs. The square-sign reflection is proved. Theorem 1.3 has actual finite sparse families, disjoint major subsets and the literal full all-cutoff maximum. The three general Section5 auxiliary statements remain partial, and the later Orlicz/ergodic/sieve applications remain unfinished. Earlier Theorems1.1/1.3 and Propositions4.19/6.21 preserve their separately recorded raw prime/distribution, Page, generic smooth multifrequency, ordinary-square and stopping hypotheses. Section7 additionally records RawTaoArcConstructionInput C and RawIWMultiplierInput C as explicit unproved independent general theorems, not Lean axioms. Actual geometry and full goodness and conditional smooth multiplier specialization are proved. The actual prime high-side comparison uses raw Tao construction, SmoothCircleBourgainInput, RawPageUniquenessInput and PagePrimeSquareDistributionInputs; its own coefficient identities, cutoffs, Page selection and approximation deductions are proved. General sampling and concrete continuous/low estimates remain unfinished. The current-paper low maximum, restricted estimate and full high/low conclusion are not external input fields.

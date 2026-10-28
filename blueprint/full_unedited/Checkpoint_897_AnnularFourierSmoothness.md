# Checkpoint 897: Actual annular C-infinity smoothness and corrected IW regularity interface

Lean proves integrability of every polynomial moment of the actual compact annular kernel, then proves the annular Fourier symbol, its source cutoff, and every bounded signed cutoff symbol are C-infinity. This checkpoint also corrects the IW interface's two regularity hypotheses from analytic top to C-infinity, as required by the independent theorem. The prior exact source and hashes are preserved; every other old proof source and all prior artifacts must remain authenticated. The changed module and all affected dependents are rebuilt before the full axiom audit. Seven negative/positive correction-validation cases pass. No prior nonzero use of the defective interface existed, and the actual prime high-side theorem does not use its predicate. No manuscript change or own-paper analytic assumption is introduced.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| AnnularFourierSmoothness.lean | 4 |

- `continuousAnnularKernel_moments`
- `annularOscillatoryModel_contDiff`
- `annularCutoffSymbol_contDiff`
- `continuousAnnularSignedSymbol_contDiff`

<!-- checkpoint-verification -->

## Verification

All 964 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4583-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2689 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 966 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed source results under their paper hypotheses remain unchanged. Lemma 3.21, both conclusions of Theorems 1.1 and 1.3, all displayed clauses of Proposition 4.19 and both clauses of Proposition 6.21 are complete checked implications under their separately recorded independent deep inputs. The square-sign reflection is proved. Theorem 1.3 has actual finite sparse families, disjoint major subsets and the literal full all-cutoff maximum. The three general Section5 auxiliary statements remain partial, and the later Orlicz/ergodic/sieve applications remain unfinished. Earlier Theorems1.1/1.3 and Propositions4.19/6.21 preserve their separately recorded raw prime/distribution, Page, generic smooth multifrequency, ordinary-square and stopping hypotheses. Section7 additionally records RawTaoArcConstructionInput C and RawIWMultiplierInput C as explicit unproved independent general theorems, not Lean axioms. Actual geometry and full goodness and conditional smooth multiplier specialization are proved. The actual prime high-side comparison uses raw Tao construction, SmoothCircleBourgainInput, RawPageUniquenessInput and PagePrimeSquareDistributionInputs; its own coefficient identities, cutoffs, Page selection and approximation deductions are proved. General sampling and concrete continuous/low estimates remain unfinished. The current-paper low maximum, restricted estimate and full high/low conclusion are not external input fields.

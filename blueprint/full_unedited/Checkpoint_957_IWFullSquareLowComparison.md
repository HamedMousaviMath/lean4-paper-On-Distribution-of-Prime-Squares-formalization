# Checkpoint 957: Actual ordinary-square IW low maximum and model comparison

The actual ordinary-square IW low operator now has the full countable near-one lp maximal bound on every integer lp input, by applying the already checked general IW theorem to the proved all-residue cyclic measure. Its exact low/high decomposition and complete-Gauss coefficient identity are checked. The actual original-cutoff ordinary circle model and its actual common-cutoff IW low operator have a proved countable L2 difference bound K*Q^(-1/4), using the existing generic smooth multifrequency comparison and the proved coefficient decay. The comparison includes varying upper denominator limits and exact cutoff geometry. The remaining step on the high side is the approximation of the actual discrete ordinary-square average by that original circle model; no own restricted or high estimate is assumed.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| IWFullSquareLowComparison.lean | 5 |

- `iwFullSquare_decomposition`
- `iw_full_square_width_symbol`
- `iw_full_square_low_maximal_bound`
- `iwFullSquareModelConstant_pos`
- `iw_full_square_model_comparison`

<!-- checkpoint-verification -->

## Verification

All 1024 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4646-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2931 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1026 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed source results under their paper hypotheses remain unchanged. Lemma 3.21, both conclusions of Theorems 1.1 and 1.3, all displayed clauses of Proposition 4.19 and both clauses of Proposition 6.21 are complete checked implications under their separately recorded independent deep inputs. The square-sign reflection is proved. Theorem 1.3 has actual finite sparse families, disjoint major subsets and the literal full all-cutoff maximum. The three general Section5 auxiliary statements remain partial, and the later Orlicz/ergodic/sieve applications remain unfinished. Earlier Theorems1.1/1.3 and Propositions4.19/6.21 preserve their separately recorded raw prime/distribution, Page, generic smooth multifrequency, ordinary-square and stopping hypotheses. Section7 additionally records RawTaoArcConstructionInput C and RawIWMultiplierInput C as explicit unproved independent general theorems, not Lean axioms. Actual geometry and full goodness and conditional smooth multiplier specialization are proved. The actual prime high-side comparison uses raw Tao construction, SmoothCircleBourgainInput, RawPageUniquenessInput and PagePrimeSquareDistributionInputs; its own coefficient identities, cutoffs, Page selection and approximation deductions are proved. General sampling and concrete continuous/low estimates remain unfinished. The current-paper low maximum, restricted estimate and full high/low conclusion are not external input fields.

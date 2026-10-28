# Checkpoint 931: Actual narrow IW finite maximum with quantitative r Crk squared cost

The actual narrow IW finite maximum is proved, for every finite complex integer input and arbitrary finite collections of integer scales at least two. Its Lp norm is at most K*r*Crk^2 times the input norm, with K=2*S*H*cutoffL1Constant^2 independent of the input, beta, period and number of scales. The proof combines the checked actual cutoff lift bound, cyclic total-variation contraction, real annular maximum, exact narrow Fourier band, general finite-target Shannon theorem, and actual diagonal identity. Membership is explicit and no own-paper maximal bound is a premise. The countable extension and assembly with the already checked short-scale maximum and countable remainder are next; the actual restricted estimate is still unfinished.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| IWNarrowFiniteMaximum.lean | 2 |

- `iwFiniteCutoffLift_size`
- `iw_narrow_finite_maximum`

<!-- checkpoint-verification -->

## Verification

All 998 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4619-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2833 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1000 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed source results under their paper hypotheses remain unchanged. Lemma 3.21, both conclusions of Theorems 1.1 and 1.3, all displayed clauses of Proposition 4.19 and both clauses of Proposition 6.21 are complete checked implications under their separately recorded independent deep inputs. The square-sign reflection is proved. Theorem 1.3 has actual finite sparse families, disjoint major subsets and the literal full all-cutoff maximum. The three general Section5 auxiliary statements remain partial, and the later Orlicz/ergodic/sieve applications remain unfinished. Earlier Theorems1.1/1.3 and Propositions4.19/6.21 preserve their separately recorded raw prime/distribution, Page, generic smooth multifrequency, ordinary-square and stopping hypotheses. Section7 additionally records RawTaoArcConstructionInput C and RawIWMultiplierInput C as explicit unproved independent general theorems, not Lean axioms. Actual geometry and full goodness and conditional smooth multiplier specialization are proved. The actual prime high-side comparison uses raw Tao construction, SmoothCircleBourgainInput, RawPageUniquenessInput and PagePrimeSquareDistributionInputs; its own coefficient identities, cutoffs, Page selection and approximation deductions are proved. General sampling and concrete continuous/low estimates remain unfinished. The current-paper low maximum, restricted estimate and full high/low conclusion are not external input fields.

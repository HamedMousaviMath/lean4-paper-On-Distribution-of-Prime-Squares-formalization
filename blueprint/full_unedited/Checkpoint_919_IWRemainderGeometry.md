# Checkpoint 919: Exact IW transition geometry and summable remainder decay

Lean proves the full scalar geometry needed for countable cutoff-remainder summation. The actual narrow width has a positive inverse b, satisfies 2a<=b and b>=2, and its exact transition scale is at least two. At the literal scales 2^j*Nstar the interpolation factor (b/N^2)^(1/r) is bounded by exp(-1/r)^j; the geometric sum is at most 2r uniformly for integer r>=2. These statements use the already proved exact transition bounds, not an asymptotic replacement or a chosen unverified threshold. No external theorem is introduced. The next step combines this geometry with the checked actual integer IW remainder and countable Lp majorant.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| IWRemainderGeometry.lean | 5 |

- `iwRemainderRatio_bounds`
- `iwRemainderRatio_sum_bound`
- `iwNarrow_inverse_geometry`
- `iwTransitionScale_two_le`
- `iw_transition_remainder_decay`

<!-- checkpoint-verification -->

## Verification

All 986 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4606-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2764 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 988 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed source results under their paper hypotheses remain unchanged. Lemma 3.21, both conclusions of Theorems 1.1 and 1.3, all displayed clauses of Proposition 4.19 and both clauses of Proposition 6.21 are complete checked implications under their separately recorded independent deep inputs. The square-sign reflection is proved. Theorem 1.3 has actual finite sparse families, disjoint major subsets and the literal full all-cutoff maximum. The three general Section5 auxiliary statements remain partial, and the later Orlicz/ergodic/sieve applications remain unfinished. Earlier Theorems1.1/1.3 and Propositions4.19/6.21 preserve their separately recorded raw prime/distribution, Page, generic smooth multifrequency, ordinary-square and stopping hypotheses. Section7 additionally records RawTaoArcConstructionInput C and RawIWMultiplierInput C as explicit unproved independent general theorems, not Lean axioms. Actual geometry and full goodness and conditional smooth multiplier specialization are proved. The actual prime high-side comparison uses raw Tao construction, SmoothCircleBourgainInput, RawPageUniquenessInput and PagePrimeSquareDistributionInputs; its own coefficient identities, cutoffs, Page selection and approximation deductions are proved. General sampling and concrete continuous/low estimates remain unfinished. The current-paper low maximum, restricted estimate and full high/low conclusion are not external input fields.

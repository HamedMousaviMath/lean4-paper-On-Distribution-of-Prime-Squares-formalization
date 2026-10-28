# Checkpoint 950: Actual full von Mangoldt restricted maximal and truncated modular estimates

The actual full von Mangoldt square maximal operator, taking the genuine supremum over every integer cutoff N>=2, now has the restricted Psi_C estimate. Lean transfers the proved annular estimate by the proved factor-four pointwise comparison and checked gauge doubling. It also instantiates the earlier restricted-to-modular proof: every finitely supported complex input has a finite actual superlevel set and the explicit truncated Orlicz cardinal bound. Thus the current-paper restricted bound is no longer an assumed premise for this arithmetic family. All independent general analytic and prime-distribution hypotheses remain explicit; this is a complete implication for the von Mangoldt family, not yet the full printed three-family Theorem7.2.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| IWPrimeFullRestrictedGauge.lean | 2 |

- `iw_prime_full_restricted_gauge`
- `iw_prime_full_modular_estimates`

<!-- checkpoint-verification -->

## Verification

All 1017 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4639-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2900 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1019 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed source results under their paper hypotheses remain unchanged. Lemma 3.21, both conclusions of Theorems 1.1 and 1.3, all displayed clauses of Proposition 4.19 and both clauses of Proposition 6.21 are complete checked implications under their separately recorded independent deep inputs. The square-sign reflection is proved. Theorem 1.3 has actual finite sparse families, disjoint major subsets and the literal full all-cutoff maximum. The three general Section5 auxiliary statements remain partial, and the later Orlicz/ergodic/sieve applications remain unfinished. Earlier Theorems1.1/1.3 and Propositions4.19/6.21 preserve their separately recorded raw prime/distribution, Page, generic smooth multifrequency, ordinary-square and stopping hypotheses. Section7 additionally records RawTaoArcConstructionInput C and RawIWMultiplierInput C as explicit unproved independent general theorems, not Lean axioms. Actual geometry and full goodness and conditional smooth multiplier specialization are proved. The actual prime high-side comparison uses raw Tao construction, SmoothCircleBourgainInput, RawPageUniquenessInput and PagePrimeSquareDistributionInputs; its own coefficient identities, cutoffs, Page selection and approximation deductions are proved. General sampling and concrete continuous/low estimates remain unfinished. The current-paper low maximum, restricted estimate and full high/low conclusion are not external input fields.

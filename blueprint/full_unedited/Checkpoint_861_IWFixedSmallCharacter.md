# Checkpoint 861: Actual fixed small-character selection and IW period divisibility

Lean now constructs the fixed small-conductor Page datum used by the low model. It proves uniqueness across all scales in the fixed conductor region directly from the existing raw Page theorem, retaining the original scale-by-scale activity and allowing inactivity. It also proves that every small denominator q>=2 divides the actual IW period, using coverage of the rational point 1/q; hence the selected small character can actually be induced to that period. Neither the existence of a fixed character nor its period divisibility is left as a current-paper external premise.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| IWFixedSmallCharacter.lean | 4 |

- `iw_period_divisible_small`
- `page_zero_in_fixed_region`
- `fixed_small_page_datum`
- `fixed_small_page_conductor_period`

<!-- checkpoint-verification -->

## Verification

All 928 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4547-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2552 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 930 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed source results under their paper hypotheses remain unchanged. Lemma 3.21, both conclusions of Theorems 1.1 and 1.3, all displayed clauses of Proposition 4.19 and both clauses of Proposition 6.21 are complete checked implications under their separately recorded independent deep inputs. The square-sign reflection is proved. Theorem 1.3 has actual finite sparse families, disjoint major subsets and the literal full all-cutoff maximum. The three general Section5 auxiliary statements remain partial, and the later Orlicz/ergodic/sieve applications remain unfinished. Proposition 4.19 consumes PrimeAsymptoticInputs, the refined PagePrimeSquareDistributionInputs c, RawPageUniquenessInput c and SmoothCircleBourgainInput C. These are independent raw analytic/data hypotheses, not own-paper operator conclusions or new Lean axioms. Theorem 1.1 retains its separately recorded older fixed-scale inputs and independent ordinary-square global decomposition; reflection is proved. Sparse applications additionally record OrdinarySquareStoppingInput CS and IndependentPrimeMaximalInput as explicit independent analytic boundaries. Their existence and the exact normalization/support/sign adaptations remain unproved; neither predicate contains this paper's endpoint or sparse conclusion. Section7 additionally records the independent RawTaoArcConstructionInput C, used only to obtain actual finite IW frequency geometry. Its existence is unproved; multiplier, sampling, low and high norm estimates are not fields and remain unfinished.

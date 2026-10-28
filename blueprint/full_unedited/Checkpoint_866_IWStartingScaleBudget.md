# Checkpoint 866: Starting-scale budget proved from the manuscript exponential scale

The starting-scale budget in the quantitative model comparison is now proved from the manuscript's exponential scale, with an explicit constant 25. For C_*>=e, Lean proves log B>=1, log(epsilon^(-1))<=17*r*log B, and (Q+1)^2*epsilon^(-1)*Q<=exp(25*((log Q)^2+r*log B)). Consequently any integer M>=2 above this exponential threshold satisfies the squared-size budget needed to absorb the small-denominator cutoff difference. Thus the coarse finite-count estimate does fit the source's permitted sufficiently large absolute constant; no extra growth condition is being silently imposed.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| IWStartingScaleBudget.lean | 4 |

- `iwDenominatorBound_log_one_le`
- `iwCutoffScale_log_bound`
- `iw_starting_budget_exp_bound`
- `iw_starting_budget_of_source_scale`

<!-- checkpoint-verification -->

## Verification

All 933 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4552-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2575 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 935 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed source results under their paper hypotheses remain unchanged. Lemma 3.21, both conclusions of Theorems 1.1 and 1.3, all displayed clauses of Proposition 4.19 and both clauses of Proposition 6.21 are complete checked implications under their separately recorded independent deep inputs. The square-sign reflection is proved. Theorem 1.3 has actual finite sparse families, disjoint major subsets and the literal full all-cutoff maximum. The three general Section5 auxiliary statements remain partial, and the later Orlicz/ergodic/sieve applications remain unfinished. Proposition 4.19 consumes PrimeAsymptoticInputs, the refined PagePrimeSquareDistributionInputs c, RawPageUniquenessInput c and SmoothCircleBourgainInput C. These are independent raw analytic/data hypotheses, not own-paper operator conclusions or new Lean axioms. Theorem 1.1 retains its separately recorded older fixed-scale inputs and independent ordinary-square global decomposition; reflection is proved. Sparse applications additionally record OrdinarySquareStoppingInput CS and IndependentPrimeMaximalInput as explicit independent analytic boundaries. Their existence and the exact normalization/support/sign adaptations remain unproved; neither predicate contains this paper's endpoint or sparse conclusion. Section7 additionally records the independent RawTaoArcConstructionInput C, used only to obtain actual finite IW frequency geometry. Its existence is unproved; multiplier, sampling, low and high norm estimates are not fields and remain unfinished.

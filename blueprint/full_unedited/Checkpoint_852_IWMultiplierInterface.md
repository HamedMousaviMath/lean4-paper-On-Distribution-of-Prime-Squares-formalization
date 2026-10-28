# Checkpoint 852: Actual smooth IW multiplier interface and quantitative specialization

The independent IW multiplier boundary now acts on the actual Fourier operators, rather than unspecified normed objects. Its explicit hypothesis ranges over arbitrary good coprime finite sets, smooth compact real symbols, finite cyclic measures, and the full admissible p interval; the assertion includes actual output Lp membership and the extended-norm inequality. This is an unformalized independent theorem (Tao Theorem1.7, with finite cyclic specialization), not a new axiom and not a claim that Mathlib proves IW. Lean proves its specialization to the manuscript's checked geometry and constants. The actual finite periodized symbol has a proved real-frequency formula, and its cyclic coefficients have the proved variation bound. The smoothness and real Lp estimate for each concrete annular symbol must still be verified before using this interface; the paper's own low/high and restricted estimates are absent from the external hypothesis.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| IWMultiplierInterface.lean | 3 |

- `cyclicRationalCoefficient_norm`
- `iwCyclicSymbol_real`
- `quantitative_iw_multiplier`

<!-- checkpoint-verification -->

## Verification

All 919 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4538-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2516 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 921 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed source results under their paper hypotheses remain unchanged. Lemma 3.21, both conclusions of Theorems 1.1 and 1.3, all displayed clauses of Proposition 4.19 and both clauses of Proposition 6.21 are complete checked implications under their separately recorded independent deep inputs. The square-sign reflection is proved. Theorem 1.3 has actual finite sparse families, disjoint major subsets and the literal full all-cutoff maximum. The three general Section5 auxiliary statements remain partial, and the later Orlicz/ergodic/sieve applications remain unfinished. Proposition 4.19 consumes PrimeAsymptoticInputs, the refined PagePrimeSquareDistributionInputs c, RawPageUniquenessInput c and SmoothCircleBourgainInput C. These are independent raw analytic/data hypotheses, not own-paper operator conclusions or new Lean axioms. Theorem 1.1 retains its separately recorded older fixed-scale inputs and independent ordinary-square global decomposition; reflection is proved. Sparse applications additionally record OrdinarySquareStoppingInput CS and IndependentPrimeMaximalInput as explicit independent analytic boundaries. Their existence and the exact normalization/support/sign adaptations remain unproved; neither predicate contains this paper's endpoint or sparse conclusion. Section7 additionally records the independent RawTaoArcConstructionInput C, used only to obtain actual finite IW frequency geometry. Its existence is unproved; multiplier, sampling, low and high norm estimates are not fields and remain unfinished.

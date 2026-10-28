# Checkpoint 854: Common-cutoff factorization and contraction on each denominator band

Lean now proves the exact relation between a common narrow cutoff and the original denominator-band cutoff. When the common width lies in the band cutoff's core, the actual periodized annular symbol factors as the original annular symbol times the common cutoff. The proof treats integer periodization explicitly and rules out cross-lift contributions. For a separated denominator band, the sum of common cutoffs defines an actual integer Fourier multiplier of operator norm at most one. This is the projection needed for the IW-cutoff high tail; it is proved, rather than included in an external sampling or maximal premise.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| CommonCutoffGeometry.lean | 9 |

- `circleWidthAnnular_real`
- `common_cutoff_source_core`
- `circleAnnularSource_eq_lift`
- `circleWidthAnnular_on_source_lift`
- `common_cutoff_zero_of_source_zero`
- `circleSmoothCutoff_supported_in_source`
- `circleWidthAnnular_factorization`
- `common_circle_cutoff_norm`
- `common_circle_projection_norm`

<!-- checkpoint-verification -->

## Verification

All 921 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4540-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2528 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 923 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed source results under their paper hypotheses remain unchanged. Lemma 3.21, both conclusions of Theorems 1.1 and 1.3, all displayed clauses of Proposition 4.19 and both clauses of Proposition 6.21 are complete checked implications under their separately recorded independent deep inputs. The square-sign reflection is proved. Theorem 1.3 has actual finite sparse families, disjoint major subsets and the literal full all-cutoff maximum. The three general Section5 auxiliary statements remain partial, and the later Orlicz/ergodic/sieve applications remain unfinished. Proposition 4.19 consumes PrimeAsymptoticInputs, the refined PagePrimeSquareDistributionInputs c, RawPageUniquenessInput c and SmoothCircleBourgainInput C. These are independent raw analytic/data hypotheses, not own-paper operator conclusions or new Lean axioms. Theorem 1.1 retains its separately recorded older fixed-scale inputs and independent ordinary-square global decomposition; reflection is proved. Sparse applications additionally record OrdinarySquareStoppingInput CS and IndependentPrimeMaximalInput as explicit independent analytic boundaries. Their existence and the exact normalization/support/sign adaptations remain unproved; neither predicate contains this paper's endpoint or sparse conclusion. Section7 additionally records the independent RawTaoArcConstructionInput C, used only to obtain actual finite IW frequency geometry. Its existence is unproved; multiplier, sampling, low and high norm estimates are not fields and remain unfinished.

# Checkpoint 859: Actual small-denominator cutoff-difference maximum

The remaining small-denominator cutoff difference now has a proved actual countable maximal L2 bound. The proof compares the two real cutoffs on their common core, uses the already proved annular Fourier decay outside that core, and passes through the actual circle periodization and integer Fourier operator. For a finite frequency set Gamma the bound is 24*card(Gamma)*A*epsilon^(-1)/(pi*M^2), uniformly in variable beta. This is a deliberately coarse finite-count bound, valid without separation, whose polynomial denominator cost can be absorbed by the manuscript's sufficiently large starting scale. The absorption into Q^(-1) and the final comparison assembly are still separate proof obligations.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| IWSmallDenominatorDifference.lean | 4 |

- `annular_common_source_difference`
- `circle_annular_common_source_difference`
- `weighted_common_source_difference`
- `common_source_difference_maximum`

<!-- checkpoint-verification -->

## Verification

All 926 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4545-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2546 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 928 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed source results under their paper hypotheses remain unchanged. Lemma 3.21, both conclusions of Theorems 1.1 and 1.3, all displayed clauses of Proposition 4.19 and both clauses of Proposition 6.21 are complete checked implications under their separately recorded independent deep inputs. The square-sign reflection is proved. Theorem 1.3 has actual finite sparse families, disjoint major subsets and the literal full all-cutoff maximum. The three general Section5 auxiliary statements remain partial, and the later Orlicz/ergodic/sieve applications remain unfinished. Proposition 4.19 consumes PrimeAsymptoticInputs, the refined PagePrimeSquareDistributionInputs c, RawPageUniquenessInput c and SmoothCircleBourgainInput C. These are independent raw analytic/data hypotheses, not own-paper operator conclusions or new Lean axioms. Theorem 1.1 retains its separately recorded older fixed-scale inputs and independent ordinary-square global decomposition; reflection is proved. Sparse applications additionally record OrdinarySquareStoppingInput CS and IndependentPrimeMaximalInput as explicit independent analytic boundaries. Their existence and the exact normalization/support/sign adaptations remain unproved; neither predicate contains this paper's endpoint or sparse conclusion. Section7 additionally records the independent RawTaoArcConstructionInput C, used only to obtain actual finite IW frequency geometry. Its existence is unproved; multiplier, sampling, low and high norm estimates are not fields and remain unfinished.

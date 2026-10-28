# Checkpoint 844: Uniform integer optimization for the Ionescu-Wainger loss

The integer optimization behind the quasi-polynomial Orlicz loss is proved uniformly. For every v>=1, choose k=ceil(sqrt(v/log(exp(1)+v)))+4. Lean proves k>=4, its two-sided rounding bounds, and k log(exp(1)+v)+v/k <=12 sqrt(v log(exp(1)+v)); a weighted version has the same bound multiplied by any fixed A>=1. This admissible alternative to the source eventual floor choice handles every bounded v directly. It proves the scalar balancing step, without assuming existence of any IW model or claiming that the full r,k,Q,N0,D parameter comparison has been discharged.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| QuantitativeIWBalance.lean | 3 |

- `iwBalancedRank_bounds`
- `iwBalancedRank_optimization`
- `iwBalancedRank_weighted`

<!-- checkpoint-verification -->

## Verification

All 911 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4518-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2474 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 913 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed source results under their paper hypotheses remain unchanged. Lemma 3.21, both conclusions of Theorems 1.1 and 1.3, all displayed clauses of Proposition 4.19 and both clauses of Proposition 6.21 are complete checked implications under their separately recorded independent deep inputs. The square-sign reflection is proved. Theorem 1.3 has actual finite sparse families, disjoint major subsets and the literal full all-cutoff maximum. The three general Section5 auxiliary statements remain partial, and the later Orlicz/ergodic/sieve applications remain unfinished. Proposition 4.19 consumes PrimeAsymptoticInputs, the refined PagePrimeSquareDistributionInputs c, RawPageUniquenessInput c and SmoothCircleBourgainInput C. These are independent raw analytic/data hypotheses, not own-paper operator conclusions or new Lean axioms. Theorem 1.1 retains its separately recorded older fixed-scale inputs and independent ordinary-square global decomposition; reflection is proved. Sparse applications additionally record OrdinarySquareStoppingInput CS and IndependentPrimeMaximalInput as explicit independent analytic boundaries. Their existence and the exact normalization/support/sign adaptations remain unproved; neither predicate contains this paper's endpoint or sparse conclusion.

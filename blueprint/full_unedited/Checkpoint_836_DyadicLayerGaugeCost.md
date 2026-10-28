# Checkpoint 836: Uniform dyadic gauge costs and truncated level-set sum

The literal gauge pays for all dyadic layer costs globally. For K>=2 and every natural layer j, Lean proves Psi_C(4*2^j*(j+1)^2) <= L(C,K) Psi_(9C+4)(2^j/K) with an explicit positive constant. The proof includes the bounded layers and all dyadic endpoints. A checked finite inverse-square sum bound controls the threshold allocation, and exact layer partitioning gives the truncated modular cost summed over the actual set where |f|>lambda/K. No asymptotic sentence or unproved rearrangement of infinite sums is used.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| DyadicLayerGaugeCost.lean | 4 |

- `layerGaugeConstant_pos`
- `dyadicLayer_gauge_cost`
- `finite_inverse_square_sum`
- `functionLayer_gauge_sum`

<!-- checkpoint-verification -->

## Verification

All 903 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4510-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2432 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 905 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed source results under their paper hypotheses remain unchanged. Lemma 3.21, both conclusions of Theorems 1.1 and 1.3, all displayed clauses of Proposition 4.19 and both clauses of Proposition 6.21 are complete checked implications under their separately recorded independent deep inputs. The square-sign reflection is proved. Theorem 1.3 has actual finite sparse families, disjoint major subsets and the literal full all-cutoff maximum. The three general Section5 auxiliary statements remain partial, and the later Orlicz/ergodic/sieve applications remain unfinished. Proposition 4.19 consumes PrimeAsymptoticInputs, the refined PagePrimeSquareDistributionInputs c, RawPageUniquenessInput c and SmoothCircleBourgainInput C. These are independent raw analytic/data hypotheses, not own-paper operator conclusions or new Lean axioms. Theorem 1.1 retains its separately recorded older fixed-scale inputs and independent ordinary-square global decomposition; reflection is proved. Sparse applications additionally record OrdinarySquareStoppingInput CS and IndependentPrimeMaximalInput as explicit independent analytic boundaries. Their existence and the exact normalization/support/sign adaptations remain unproved; neither predicate contains this paper's endpoint or sparse conclusion.

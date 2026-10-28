# Checkpoint 840: Literal quantitative Ionescu-Wainger parameters and separation

The quantitative Ionescu-Wainger scalar parameters from e:IWparameters7 and e:orlicz-D are defined with their printed powers and logarithms. Lean proves 1<p_r<=4/3, the exact identities p_r-1=1/(2r-1) and 1/p_r=1-1/(2r), and the rho range, half-exponent and exact floor-rank relation for k>=4. It proves B>=1, its exact logarithm, epsilon>0 and the strict separation inequality 4 epsilon B^2<1. All are unconditional algebraic deductions; existence of the IW sets, multiplier and sampling estimates has not been supplied by an assumption or declared proved. Natural Q is enough for the later dyadic parameter choice; the full printed real-Q proposition is not awarded.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| QuantitativeIWParameters.lean | 10 |

- `iwNearOneExponent_bounds`
- `iwNearOneExponent_sub_one`
- `iwNearOneExponent_reciprocal`
- `iwRho_bounds`
- `iwRho_half`
- `iwRho_rank`
- `iwDenominatorBound_one_le`
- `iwDenominatorBound_log`
- `iwWidth_pos`
- `iwWidth_denominator_separation`

<!-- checkpoint-verification -->

## Verification

All 907 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4514-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2456 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 909 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed source results under their paper hypotheses remain unchanged. Lemma 3.21, both conclusions of Theorems 1.1 and 1.3, all displayed clauses of Proposition 4.19 and both clauses of Proposition 6.21 are complete checked implications under their separately recorded independent deep inputs. The square-sign reflection is proved. Theorem 1.3 has actual finite sparse families, disjoint major subsets and the literal full all-cutoff maximum. The three general Section5 auxiliary statements remain partial, and the later Orlicz/ergodic/sieve applications remain unfinished. Proposition 4.19 consumes PrimeAsymptoticInputs, the refined PagePrimeSquareDistributionInputs c, RawPageUniquenessInput c and SmoothCircleBourgainInput C. These are independent raw analytic/data hypotheses, not own-paper operator conclusions or new Lean axioms. Theorem 1.1 retains its separately recorded older fixed-scale inputs and independent ordinary-square global decomposition; reflection is proved. Sparse applications additionally record OrdinarySquareStoppingInput CS and IndependentPrimeMaximalInput as explicit independent analytic boundaries. Their existence and the exact normalization/support/sign adaptations remain unproved; neither predicate contains this paper's endpoint or sparse conclusion.

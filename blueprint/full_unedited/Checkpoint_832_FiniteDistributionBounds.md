# Checkpoint 832: Finite testing and actual distributional cardinal bounds

A finite-test distribution formalism is proved equivalent to finiteness and the actual level-set cardinal bound. Infinite level sets cannot silently receive cardinality zero: arbitrarily large finite subsets give a checked contradiction. Lean proves Chebyshev bounds for every positive real exponent, their actual lp-space specialization, monotonicity, the two-term distribution union estimate, and the finite-family sum estimate. These are the counting tools for Section7 high-low and layer-cake deductions. They contain no arithmetic, restricted endpoint or modular estimate as an assumed external theorem.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| FiniteDistributionBounds.lean | 9 |

- `finiteDistribution_nonneg`
- `testedDistribution_finite`
- `testedDistribution_ncard`
- `testedDistribution_iff`
- `finiteDistribution_chebyshev`
- `finiteDistribution_lp`
- `finiteDistribution_mono`
- `finiteDistribution_two`
- `finiteDistribution_finite_sum`

<!-- checkpoint-verification -->

## Verification

All 899 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4506-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2405 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 901 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed source results under their paper hypotheses remain unchanged. Lemma 3.21, both conclusions of Theorems 1.1 and 1.3, all displayed clauses of Proposition 4.19 and both clauses of Proposition 6.21 are complete checked implications under their separately recorded independent deep inputs. The square-sign reflection is proved. Theorem 1.3 has actual finite sparse families, disjoint major subsets and the literal full all-cutoff maximum. The three general Section5 auxiliary statements remain partial, and the later Orlicz/ergodic/sieve applications remain unfinished. Proposition 4.19 consumes PrimeAsymptoticInputs, the refined PagePrimeSquareDistributionInputs c, RawPageUniquenessInput c and SmoothCircleBourgainInput C. These are independent raw analytic/data hypotheses, not own-paper operator conclusions or new Lean axioms. Theorem 1.1 retains its separately recorded older fixed-scale inputs and independent ordinary-square global decomposition; reflection is proved. Sparse applications additionally record OrdinarySquareStoppingInput CS and IndependentPrimeMaximalInput as explicit independent analytic boundaries. Their existence and the exact normalization/support/sign adaptations remain unproved; neither predicate contains this paper's endpoint or sparse conclusion.

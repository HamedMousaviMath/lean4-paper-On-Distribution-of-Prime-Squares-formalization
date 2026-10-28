# Checkpoint 838: Actual square von Mangoldt and prime averaging families

All three averaging families in the printed Section7 theorem now instantiate the positive finite-family framework. They use the literal square shifts x-n^2. The von Mangoldt family uses Mathlib Lambda including prime powers and the proved Chebyshev mass bound. The ordinary-square family uses 1/N. The unweighted-prime family uses the actual primesLE finite set and Mathlib primeCounting pi(N), with exactly the normalization 1/pi(N). Their actual finite averages and countable maxima over every integer N>=2 are proved identical to the concrete formulas. The common uniform mass bound is proved without PNT. No modular, near-L1 or IW estimate is inferred from mass alone.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| ActualPositiveSquareFamilies.lean | 7 |

- `mangoldtPositiveFamily_apply`
- `ordinaryPositiveFamily_apply`
- `primePositiveFamily_apply`
- `positiveSquareFamilies_uniform_mass`
- `mangoldtPositiveFamily_maximal`
- `ordinaryPositiveFamily_maximal`
- `primePositiveFamily_maximal`

<!-- checkpoint-verification -->

## Verification

All 905 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4512-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2441 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 907 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed source results under their paper hypotheses remain unchanged. Lemma 3.21, both conclusions of Theorems 1.1 and 1.3, all displayed clauses of Proposition 4.19 and both clauses of Proposition 6.21 are complete checked implications under their separately recorded independent deep inputs. The square-sign reflection is proved. Theorem 1.3 has actual finite sparse families, disjoint major subsets and the literal full all-cutoff maximum. The three general Section5 auxiliary statements remain partial, and the later Orlicz/ergodic/sieve applications remain unfinished. Proposition 4.19 consumes PrimeAsymptoticInputs, the refined PagePrimeSquareDistributionInputs c, RawPageUniquenessInput c and SmoothCircleBourgainInput C. These are independent raw analytic/data hypotheses, not own-paper operator conclusions or new Lean axioms. Theorem 1.1 retains its separately recorded older fixed-scale inputs and independent ordinary-square global decomposition; reflection is proved. Sparse applications additionally record OrdinarySquareStoppingInput CS and IndependentPrimeMaximalInput as explicit independent analytic boundaries. Their existence and the exact normalization/support/sign adaptations remain unproved; neither predicate contains this paper's endpoint or sparse conclusion.

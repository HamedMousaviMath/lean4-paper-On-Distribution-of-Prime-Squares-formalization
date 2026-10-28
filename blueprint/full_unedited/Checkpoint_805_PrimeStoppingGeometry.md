# Checkpoint 805: Construct quarter-packed stopping children and prove actual source admissibility

Constructs the actual parent bad set by testing every integer subinterval of the fivefold parent at density threshold 64|F|/|I|. Proves quarter packing, exact covering by disjoint maximal bad components, strict decrease of their lengths and the good-point density property. For every remaining arithmetic scale N, proves the literal sourceLocalMass bound <=320|F|/|I|, uniformly over every real radius M>=N. These deductions supply admissibility rather than assuming it.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| PrimeStoppingGeometry.lean | 7 |

- `primeStoppingBadSet_subset`
- `primeStoppingBadSet_packing`
- `primeStoppingChildren_cover`
- `primeStoppingChildren_disjoint`
- `primeStoppingChildren_geometry`
- `primeStopping_good_density`
- `primeStopping_remaining_localMass`

<!-- checkpoint-verification -->

## Verification

All 872 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4479-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2291 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 874 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results under their paper hypotheses remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. Lemma 3.21, both conclusions of Theorem 1.1, all displayed clauses of Proposition 4.19 and both clauses of Proposition 6.21 are complete checked implications under their separately recorded independent deep inputs. The square-sign reflection is proved. The whole paper, the stronger printed auxiliary lemmas and the later sparse/ergodic/sieve applications remain unfinished. Proposition 4.19 consumes PrimeAsymptoticInputs, the refined PagePrimeSquareDistributionInputs c, RawPageUniquenessInput c and SmoothCircleBourgainInput C. These are independent raw analytic/data hypotheses, not own-paper operator conclusions or new Lean axioms. Theorem 1.1 retains its separately recorded older fixed-scale inputs and independent ordinary-square global decomposition; reflection is proved.

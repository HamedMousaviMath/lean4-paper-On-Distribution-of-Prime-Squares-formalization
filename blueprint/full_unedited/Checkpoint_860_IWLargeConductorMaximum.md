# Checkpoint 860: Actual Q-to-minus-one-quarter changing large-conductor maximum

The changing large-conductor exceptional contribution now has an actual countable maximal L2 majorant of size K*Q^(-1/4). Lean keeps the original rational annular symbols, permits the exceptional character to vary with scale, and proves uniformity by splitting the Gauss decay between Q, the conductor and the remaining denominator. The already checked Page uniqueness theorem bounds the sum over conductor classes. No fixed-character substitution and no current-paper exceptional maximal estimate is assumed. The only hypotheses are the independently recorded smooth multifrequency and raw Page uniqueness inputs.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| IWLargeConductorMaximum.lean | 2 |

- `iw_conductor_denominator_power`
- `iw_large_conductor_maximum`

<!-- checkpoint-verification -->

## Verification

All 927 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4546-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2548 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 929 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed source results under their paper hypotheses remain unchanged. Lemma 3.21, both conclusions of Theorems 1.1 and 1.3, all displayed clauses of Proposition 4.19 and both clauses of Proposition 6.21 are complete checked implications under their separately recorded independent deep inputs. The square-sign reflection is proved. Theorem 1.3 has actual finite sparse families, disjoint major subsets and the literal full all-cutoff maximum. The three general Section5 auxiliary statements remain partial, and the later Orlicz/ergodic/sieve applications remain unfinished. Proposition 4.19 consumes PrimeAsymptoticInputs, the refined PagePrimeSquareDistributionInputs c, RawPageUniquenessInput c and SmoothCircleBourgainInput C. These are independent raw analytic/data hypotheses, not own-paper operator conclusions or new Lean axioms. Theorem 1.1 retains its separately recorded older fixed-scale inputs and independent ordinary-square global decomposition; reflection is proved. Sparse applications additionally record OrdinarySquareStoppingInput CS and IndependentPrimeMaximalInput as explicit independent analytic boundaries. Their existence and the exact normalization/support/sign adaptations remain unproved; neither predicate contains this paper's endpoint or sparse conclusion. Section7 additionally records the independent RawTaoArcConstructionInput C, used only to obtain actual finite IW frequency geometry. Its existence is unproved; multiplier, sampling, low and high norm estimates are not fields and remain unfinished.

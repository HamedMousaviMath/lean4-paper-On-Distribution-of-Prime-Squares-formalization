# Checkpoint 811: Balance the local prime low high and maximal-error terms uniformly in density

Proves the uniform stopping scalar balance for the actual low, high and maximal-error terms, with every coefficient strictly above the sharp leading coefficient. The chosen dyadic Q obeys log Q <= B paperLog(delta) with one fixed B, and the bound includes the full bounded-density range through an explicit compact estimate. No optimization or cutoff-choice conclusion is assumed.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| LocalPrimeScalarBalance.lean | 2 |

- `localPrimeScalar_eq`
- `exists_localPrime_balance`

<!-- checkpoint-verification -->

## Verification

All 878 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4485-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2318 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 880 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results under their paper hypotheses remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. Lemma 3.21, both conclusions of Theorem 1.1, all displayed clauses of Proposition 4.19 and both clauses of Proposition 6.21 are complete checked implications under their separately recorded independent deep inputs. The square-sign reflection is proved. The whole paper, the stronger printed auxiliary lemmas and the later sparse/ergodic/sieve applications remain unfinished. Proposition 4.19 consumes PrimeAsymptoticInputs, the refined PagePrimeSquareDistributionInputs c, RawPageUniquenessInput c and SmoothCircleBourgainInput C. These are independent raw analytic/data hypotheses, not own-paper operator conclusions or new Lean axioms. Theorem 1.1 retains its separately recorded older fixed-scale inputs and independent ordinary-square global decomposition; reflection is proved. Sparse applications additionally record OrdinarySquareStoppingInput CS and IndependentPrimeMaximalInput as explicit independent analytic boundaries. Their existence and the exact normalization/support/sign adaptations remain unproved; neither predicate contains this paper's endpoint or sparse conclusion.

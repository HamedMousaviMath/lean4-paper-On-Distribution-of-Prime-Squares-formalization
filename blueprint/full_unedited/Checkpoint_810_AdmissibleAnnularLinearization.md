# Checkpoint 810: Prove exact admissible linearization and the sparse deduction from a local estimate

Proves exact finite linearization of the remaining-scale maximum on its actual active test set. The chosen dyadic scale attains that maximum, satisfies the parent spatial cutoff and the proved local-average admissibility bound. Combines the actual one-generation recursion with the terminating laminar construction to obtain a genuine finite 3/4-sparse bound from an explicit admissible local estimate. That local estimate remains a deduction to be supplied from the recorded analytic inputs, not a newly assumed independent result.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| AdmissibleAnnularLinearization.lean | 5 |

- `finite_positive_pairing_norm`
- `annularDyadicValue_positive`
- `primeRemainingScale_linearized`
- `primeAnnularSparseStep`
- `primeAnnularSparse_from_local`

<!-- checkpoint-verification -->

## Verification

All 877 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4484-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2316 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 879 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results under their paper hypotheses remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. Lemma 3.21, both conclusions of Theorem 1.1, all displayed clauses of Proposition 4.19 and both clauses of Proposition 6.21 are complete checked implications under their separately recorded independent deep inputs. The square-sign reflection is proved. The whole paper, the stronger printed auxiliary lemmas and the later sparse/ergodic/sieve applications remain unfinished. Proposition 4.19 consumes PrimeAsymptoticInputs, the refined PagePrimeSquareDistributionInputs c, RawPageUniquenessInput c and SmoothCircleBourgainInput C. These are independent raw analytic/data hypotheses, not own-paper operator conclusions or new Lean axioms. Theorem 1.1 retains its separately recorded older fixed-scale inputs and independent ordinary-square global decomposition; reflection is proved. Sparse applications additionally record OrdinarySquareStoppingInput CS and IndependentPrimeMaximalInput as explicit independent analytic boundaries. Their existence and the exact normalization/support/sign adaptations remain unproved; neither predicate contains this paper's endpoint or sparse conclusion.

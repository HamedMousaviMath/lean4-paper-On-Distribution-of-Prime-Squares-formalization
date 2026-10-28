# Checkpoint 819: Prove the actual sharp admissible prime-square local endpoint

Proves the actual admissible prime-square local endpoint, uniformly in every parent interval, finite input/reference/test sets and varying dyadic arithmetic scale. The density retains the larger reference test set. Small scales use the proved prime-to-ordinary comparison and the independent ordinary low/high input; large scales use the exact common Proposition 4.19 family and the proved scalar balance. The sharp coefficient is every cstar>4sqrt(3)/9, all bounded densities are included, and fixed logarithmic powers are absorbed by the actual paper Phi. No local endpoint conclusion is an assumed input.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| PrimeStoppingLocalEndpoint.lean | 2 |

- `finiteSetDensity_five_bounds`
- `primeStopping_local_endpoint`

<!-- checkpoint-verification -->

## Verification

All 886 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4493-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2332 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 888 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results under their paper hypotheses remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. Lemma 3.21, both conclusions of Theorem 1.1, all displayed clauses of Proposition 4.19 and both clauses of Proposition 6.21 are complete checked implications under their separately recorded independent deep inputs. The square-sign reflection is proved. The whole paper, the stronger printed auxiliary lemmas and the later sparse/ergodic/sieve applications remain unfinished. Proposition 4.19 consumes PrimeAsymptoticInputs, the refined PagePrimeSquareDistributionInputs c, RawPageUniquenessInput c and SmoothCircleBourgainInput C. These are independent raw analytic/data hypotheses, not own-paper operator conclusions or new Lean axioms. Theorem 1.1 retains its separately recorded older fixed-scale inputs and independent ordinary-square global decomposition; reflection is proved. Sparse applications additionally record OrdinarySquareStoppingInput CS and IndependentPrimeMaximalInput as explicit independent analytic boundaries. Their existence and the exact normalization/support/sign adaptations remain unproved; neither predicate contains this paper's endpoint or sparse conclusion.

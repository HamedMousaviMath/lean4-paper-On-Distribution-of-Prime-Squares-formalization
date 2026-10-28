# Checkpoint 373: Uniform square-energy summation over the actual active rational centers

For one denominator block, actual broad support leaves at most four active canonical centers independent of the dyadic arithmetic index. Summing the individual finite time energies gives a full rational-sum energy at most (4A)^2, with every inactive term exactly zero. The bound is independent of the total number of rational centers.


## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| DyadicSparseSquareEnergy.lean | 1 |

- `dyadic_sparse_square_energy`

<!-- checkpoint-verification -->

## Verification

All 440 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4047-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 1546 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 442 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. Published Ren and Ghosh quadratic exponential-sum estimates, when consumed, remain displayed raw theorem hypotheses; the progression-prefix estimate also remains an explicit unproved input. No own-paper analytic conclusion is assumed.

# Checkpoint 59: Absolute convergence and bounds for all-input l1 convolution

Convolution by an arbitrary uniformly bounded integer kernel is defined for every l1 input by an actual infinite sum. The series is proved absolutely summable at each output point by comparison with the l1 norm. Its norm is bounded by B times the input l1 norm. This removes the finite-input restriction from the earlier estimate and justifies the infinite convolution rather than assigning a value without proving convergence.


## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| KernelL1Summation.lean | 2 |

- `kernelL1_summable`
- `kernelL1Sum_bound`

<!-- checkpoint-verification -->

## Verification

All 126 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 3645-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 882 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 128 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. The already displayed raw progression-prefix estimate is consumed as a theorem hypothesis; it remains unproved. No new external analytic estimate or own-paper lemma is assumed.

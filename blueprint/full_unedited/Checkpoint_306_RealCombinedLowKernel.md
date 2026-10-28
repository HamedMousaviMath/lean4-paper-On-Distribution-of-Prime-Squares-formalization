# Checkpoint 306: The actual combined real-cutoff low symbol and its inverse kernel

The actual combined real-cutoff low symbol and its inverse kernel. Ordinary and optional induced exceptional kernels are combined with the exact subtraction sign. For N>=2, real Q>=2, a quadratic base character, beta<=1 and 2Q<=N^2, the kernel has a uniform 2*C_low*Q*log(2Q)/N^2 rapid-decay bound, and the finite local estimate has constant 8*C_low*Q*log(2Q). The l1-to-linfinity operator estimate holds for all l1 inputs and is uniform in the global denominator truncation. No deep analytic input is used.


## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| RealCombinedLowKernel.lean | 1 |

- `realCombinedLowModel_kernel`

<!-- checkpoint-verification -->

## Verification

All 373 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 3980-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 1429 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 375 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. Published Ren and Ghosh quadratic exponential-sum estimates, when consumed, remain displayed raw theorem hypotheses; the progression-prefix estimate also remains an explicit unproved input. No own-paper analytic conclusion is assumed.

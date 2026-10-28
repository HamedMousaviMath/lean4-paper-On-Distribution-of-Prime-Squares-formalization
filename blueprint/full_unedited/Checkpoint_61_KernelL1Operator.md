# Checkpoint 61: A genuine bounded linear l1-to-linfinity convolution operator

Bounded-kernel convolution is now a genuine complex continuous linear map from integer l1 to integer linfinity. Complex linearity is proved directly from the convergent series, the application formula is the actual convolution sum, and its operator norm is at most the kernel bound B. The construction does not assume positivity or finite kernel support, so it applies to smooth Fourier-cutoff inverse kernels whose spatial support need not be compact.


## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| KernelL1Operator.lean | 2 |

- `kernelL1Operator_apply`
- `kernelL1Operator_norm`

<!-- checkpoint-verification -->

## Verification

All 128 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 3647-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 886 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 130 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. The already displayed raw progression-prefix estimate is consumed as a theorem hypothesis; it remains unproved. No new external analytic estimate or own-paper lemma is assumed.

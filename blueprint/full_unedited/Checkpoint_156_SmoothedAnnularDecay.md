# Checkpoint 156: Uniform spatial decay after annular smoothing

Proves the actual smoothed annular kernel is bounded by 2^K*C_K/(2a) times (1+|x|/N^2)^(-K), for 0<a<=N^2, N>=2 and beta<=1. This is an unconditional physical-space estimate. Its Fourier identification and the arithmetic low-kernel assembly remain separate obligations.


## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| SmoothedAnnularDecay.lean | 1 |

- `smoothedAnnularKernel_decay`

<!-- checkpoint-verification -->

## Verification

All 223 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 3830-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 1131 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 225 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. Published Ren and Ghosh quadratic exponential-sum estimates, when consumed, remain displayed raw theorem hypotheses; the progression-prefix estimate also remains an explicit unproved input. No own-paper analytic conclusion is assumed.

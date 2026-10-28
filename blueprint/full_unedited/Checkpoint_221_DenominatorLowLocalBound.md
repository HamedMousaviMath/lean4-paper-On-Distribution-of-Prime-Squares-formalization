# Checkpoint 221: The local low estimate for the genuine Fourier multiplier

The local low estimate for the genuine Fourier multiplier. This module proves the stated construction or operator consequence for genuine continuous circle symbols, with the actual Gauss/twisted coefficients and the source annular smoothing. The parameter domain is natural N,Q>=2 with 2Q<=N^2, positive conductor, a quadratic character, beta<=1 and the explicit contributing-denominator width conditions. No analytic low estimate is assumed. The exact identification with the earlier rational-indexed circle approximation model, general real cutoffs, the sharp high estimates and Theorem 1.1 remain separate obligations. The Lean declarations specify every condition and normalization.


## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| DenominatorLowLocalBound.lean | 2 |

- `denominatorCircleLow_finite_convolution`
- `denominatorCircleLow_local_finite`

<!-- checkpoint-verification -->

## Verification

All 288 project modules and the root were freshly rebuilt: 3895 jobs pass without warnings/errors. All 1259 named theorems pass the complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound. The source scan checks 290 Lean files. Exact unique import/audit coverage and unchanged frozen source hashes are checked before packaging. There are no placeholders or added mathematical axioms.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. Published Ren and Ghosh quadratic exponential-sum estimates, when consumed, remain displayed raw theorem hypotheses; the progression-prefix estimate also remains an explicit unproved input. No own-paper analytic conclusion is assumed.

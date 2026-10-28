# Checkpoint 171: A full finite-input local convolution estimate

For every complex kernel with norm bounded by (A/H)*(1+|z|/H)^(-10), proves the finite complex convolution is at most 4A times the dyadic local-mass envelope of input magnitudes. This fully proves the generic harmonic-analysis shell step in Proposition 6.14; identifying and assembling the source low kernel remain separate obligations. This checkpoint performs a fresh full rebuild.


## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| FiniteLocalConvolution.lean | 1 |

- `finiteConvolution_local_mass`

<!-- checkpoint-verification -->

## Verification

All 238 project modules and the root were freshly rebuilt: 3845 jobs pass without warnings/errors. All 1163 named theorems pass the complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound. The source scan checks 240 Lean files. Exact unique import/audit coverage and unchanged frozen source hashes are checked before packaging. There are no placeholders or added mathematical axioms.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. Published Ren and Ghosh quadratic exponential-sum estimates, when consumed, remain displayed raw theorem hypotheses; the progression-prefix estimate also remains an explicit unproved input. No own-paper analytic conclusion is assumed.

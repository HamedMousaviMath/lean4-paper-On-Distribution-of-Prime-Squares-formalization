# Checkpoint 600: Uniform single-scale multiplier bounds do not imply a countable maximal bound

Closes this milestone with an explicit counterexample using the actual continuous circle symbols and existing integer Fourier multipliers: every character multiplier has operator norm at most one, yet their outputs on the unit mass at zero have no real l2 pointwise majorant. This proves why the remaining full high maximum needs a separate argument. The counterexample concerns a general family, not a counterexample to the manuscript theorem. Theorem 1.1, Proposition 4.19 and the source multifrequency interval estimate remain open.


## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| UniformMultiplierNormCounterexample.lean | 1 |

- `uniformMultiplier_norm_not_maximal`

<!-- checkpoint-verification -->

## Verification

All 667 project modules and the root were freshly rebuilt: 4274 jobs pass without warnings/errors. All 1807 named theorems pass the complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound. The source scan checks 669 Lean files. Exact unique import/audit coverage and unchanged frozen source hashes are checked before packaging. There are no placeholders or added mathematical axioms.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. Published Ren and Ghosh quadratic exponential-sum estimates, when consumed, remain displayed raw theorem hypotheses; the progression-prefix estimate also remains an explicit unproved input. No own-paper analytic conclusion is assumed.

# Checkpoint 471: The exact conductor collar set for arbitrary nonnegative source radius

Removes the assumption that the global source radius contains the whole exceptional collar. The source set is exactly the full conductor collar clipped at the actual global radius, including when the conductor lies beyond that radius.

The claims are exactly the displayed Lean declarations. No new axiom or manuscript conclusion is assumed. The sharp full high maximal bound, Proposition 4.19 and Theorem 1.1 remain open.


## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| ClippedSourceConductorCenters.lean | 1 |

- `clipped_source_conductor_centers`

<!-- checkpoint-verification -->

## Verification

All 538 project modules and the root were freshly rebuilt: 4145 jobs pass without warnings/errors. All 1660 named theorems pass the complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound. The source scan checks 540 Lean files. Exact unique import/audit coverage and unchanged frozen source hashes are checked before packaging. There are no placeholders or added mathematical axioms.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. Published Ren and Ghosh quadratic exponential-sum estimates, when consumed, remain displayed raw theorem hypotheses; the progression-prefix estimate also remains an explicit unproved input. No own-paper analytic conclusion is assumed.

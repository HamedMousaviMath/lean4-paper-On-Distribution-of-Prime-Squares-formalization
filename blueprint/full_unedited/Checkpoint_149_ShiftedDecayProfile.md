# Checkpoint 149: Decay after a bounded spatial translation

Proves the translated spatial decay inequality when the averaging measure is supported in |y| <= C H. The precise bound is profile_H,K(x-y) <= (1+C)^K profile_H,K(x), with all positivity and scale conditions present. This supplies the support comparison needed to convolve a decaying cutoff kernel with the annular square measure.


## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| ShiftedDecayProfile.lean | 2 |

- `decayProfile_shift_base`
- `decayProfile_shift_bound`

<!-- checkpoint-verification -->

## Verification

All 216 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 3741-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 1113 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 218 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. Published Ren and Ghosh quadratic exponential-sum estimates, when consumed, remain displayed raw theorem hypotheses; the progression-prefix estimate also remains an explicit unproved input. No own-paper analytic conclusion is assumed.

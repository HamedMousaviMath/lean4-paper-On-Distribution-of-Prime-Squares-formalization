# Checkpoint 127: Weighted real-power finite tails

For every fixed real s>=2 and j>=J, Lean splits (j+1)^(-s) into a nonincreasing weight and a reciprocal square. The weight is bounded by (J+1)^(2-s), giving

    sum_(J<=j<K) (j+1)^(-s) <= 2*(J+1)^(1-s).

All real-power identities and positivity conditions are proved. The bound holds for arbitrary natural endpoints, including empty intervals and the starting exponent zero. It retains the exact tail exponent needed for a maximal-error estimate with arbitrary logarithmic saving.

The statement is an unconditional scalar series bound, not an assumed operator inequality.


## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| WeightedPowerFiniteTail.lean | 2 |

- `weighted_power_reciprocal_bound`
- `weighted_power_finite_tail`

<!-- checkpoint-verification -->

## Verification

All 194 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 3719-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 1055 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 196 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. Published Ren and Ghosh quadratic exponential-sum estimates, when consumed, remain displayed raw theorem hypotheses; the progression-prefix estimate also remains an explicit unproved input. No own-paper analytic conclusion is assumed.

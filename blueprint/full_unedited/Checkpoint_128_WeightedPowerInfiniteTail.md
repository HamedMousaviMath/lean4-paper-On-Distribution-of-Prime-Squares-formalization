# Checkpoint 128: Summability and quantitative weighted infinite tails

The weighted finite-tail estimate is passed to the infinite nonnegative series. For every real s>=2 and every natural starting exponent J, Lean proves summability and

    sum_j (J+j+1)^(-s) <= 2*(J+1)^(1-s).

There is no dependence on an unbounded finite truncation and no interchange of conditionally convergent sums. The proof uses bounded nonnegative partial sums, so both existence and the quantitative tail are checked.

This is the scalar summability input for the countable l2 envelope constructed next.


## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| WeightedPowerInfiniteTail.lean | 2 |

- `weighted_power_shift_summable`
- `weighted_power_infinite_tail`

<!-- checkpoint-verification -->

## Verification

All 195 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 3720-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 1057 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 197 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. Published Ren and Ghosh quadratic exponential-sum estimates, when consumed, remain displayed raw theorem hypotheses; the progression-prefix estimate also remains an explicit unproved input. No own-paper analytic conclusion is assumed.

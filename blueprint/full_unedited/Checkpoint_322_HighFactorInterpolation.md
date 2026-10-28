# Checkpoint 322: Fractional-power interpolation of the actual high size and tail bounds

Fractional-power interpolation of the actual high size and tail bounds. The original centered high symbol is retained. The effective exceptional cutoff is Q*q0/B0, and the source quotient condition and smoothing width are proved algebraically identical to that cutoff. Interpolation of the proved size and decay bounds gives a genuine fractional Q saving, with the complementary denominator power retained for the coming dyadic sum. No high estimate is assumed.


## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| HighFactorInterpolation.lean | 3 |

- `min_one_le_fractional_power`
- `high_power_product`
- `two_bounds_rpow_interpolate`

<!-- checkpoint-verification -->

## Verification

All 389 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 3996-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 1470 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 391 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. Published Ren and Ghosh quadratic exponential-sum estimates, when consumed, remain displayed raw theorem hypotheses; the progression-prefix estimate also remains an explicit unproved input. No own-paper analytic conclusion is assumed.

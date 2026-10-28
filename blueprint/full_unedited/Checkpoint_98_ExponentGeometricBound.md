# Checkpoint 98: Uniform prime-power exponent growth

This is the first step of an unconditional divisor-growth proof needed to retain Ren's divisor prefactor. For every fixed real ratio r>1, Lean proves a single constant A>=1 such that n+1<=A*r^n for every natural exponent n, including n=0 and the whole finite initial range. The eventual estimate is obtained from a proved Mathlib asymptotic limit; the early exponents are bounded explicitly by the selected threshold. No number-theoretic hypothesis enters.

Real powers commute with natural powers on nonnegative bases. Applying the geometric estimate at ratio 2^epsilon, and using p>=2, gives a constant A independent of the prime p and exponent n such that n+1<=A*(p^n)^epsilon. The exponent epsilon is a fixed positive real number, not a parameter chosen with the denominator or scale. This is the local prime-power inequality that will be multiplied over the factorization of q.

This checkpoint proves these uniform local growth statements only. The full divisor count and its 3/2 power are addressed subsequently. It does not assume a divisor bound, PNT, a progression estimate or an exponential-sum theorem, and it does not close the minor-arc or main theorem gaps on its own.


## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| ExponentGeometricBound.lean | 3 |

- `exponent_add_one_le_geometric`
- `rpow_nat_power_comm`
- `primePower_exponent_bound`

<!-- checkpoint-verification -->

## Verification

All 165 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 3684-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 976 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 167 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. Published Ren and Ghosh quadratic exponential-sum estimates, when consumed, remain displayed raw theorem hypotheses; the progression-prefix estimate also remains an explicit unproved input. No own-paper analytic conclusion is assumed.

# Checkpoint 147: The truncated ordinary low arithmetic sum

The ordinary low-kernel arithmetic estimate is connected to the exact truncated denominator sum. Lean proves that the smooth absolute Cohen series is summable using its finite divisor support, dominates every finite sum whose prime factors lie below the cutoff, and gives an explicit uniform bound for the sum over 1 <= q <= Q by (cohenLogConstant/2)*log(Q+1). This is unconditional, uses the genuine correlation, and does not assume Mertens or the low-kernel conclusion. It supplies the arithmetic input for Proposition 6.14; the spatial kernel and source Fourier bridges remain to be proved.


## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| TruncatedCohenBound.lean | 3 |

- `smoothCohen_summable`
- `finite_cohen_sum_le_smooth`
- `truncated_cohen_log_bound`

<!-- checkpoint-verification -->

## Verification

All 214 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 3739-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 1107 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 216 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. Published Ren and Ghosh quadratic exponential-sum estimates, when consumed, remain displayed raw theorem hypotheses; the progression-prefix estimate also remains an explicit unproved input. No own-paper analytic conclusion is assumed.

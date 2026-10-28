# Checkpoint 122: Monotonicity of the allowed Q range and source cutoff

The allowed Q range is proved stable as the arithmetic scale increases. The coefficient min(c/7,1)/8 is positive for c>0, and monotonicity of log and sqrt shows that a Q allowed at N is allowed at every M>=N>=1.

The source cutoff itself is also monotone in N on N>=1. This follows from monotonicity of log, the fixed positive real power 1/10, exp and max. These facts allow one Q and one starting-scale condition to be used along an entire dyadic tail, rather than imposing unrelated conditions at each scale.

The proofs are unconditional scalar geometry. They introduce no prime-distribution or operator-norm assumptions and do not claim the remaining sharp high/low estimates.


## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| SourceRangeMonotonicity.lean | 3 |

- `sourceQCoefficient_pos`
- `sourceQRange_upward`
- `sourceMajorArcScale_mono_N`

<!-- checkpoint-verification -->

## Verification

All 189 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 3711-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 1041 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 191 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. Published Ren and Ghosh quadratic exponential-sum estimates, when consumed, remain displayed raw theorem hypotheses; the progression-prefix estimate also remains an explicit unproved input. No own-paper analytic conclusion is assumed.

# Checkpoint 82: Genuine low l1 and high l2 operators with finite convolution formulas

The low circle symbol defines an actual bounded linear operator from integer l1 into linfinity; the high symbol defines an actual l2 Fourier multiplier. On every finite complex input both operators are proved to equal convolution with their respective genuine inverse kernels. This aligns the two different input norms with a common spatial decomposition and avoids treating formal symbols as already-defined convolution operators.


## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| CircleHighLowOperators.lean | 2 |

- `circleLowOperator_finite`
- `circleHighOperator_finite`

<!-- checkpoint-verification -->

## Verification

All 149 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 3668-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 927 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 151 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. The already displayed raw progression-prefix estimate is consumed as a theorem hypothesis; it remains unproved. No new external analytic estimate or own-paper lemma is assumed.

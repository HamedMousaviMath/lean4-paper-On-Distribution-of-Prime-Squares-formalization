# Checkpoint 116: A uniform source-scale complementary minor budget

The complementary minor budget is proved uniformly small at the actual source scale. The logarithmic factor in Ren's term is bounded by R^(1/12), turning that contribution into renSourceConstant(C)*R^(-1/3). Ghosh's contribution is ghoshSourceConstant(B)*R^(-1/4). Their sum is eventually at most R^(-1/6), uniformly over Q, for fixed C,B,d>=0.

Substituting the already proved source-scale logarithmic rate gives the desired Q^(-1/2)*(1+log N)^(-A) bound with factor 2^A, for every A>=0 and Q>=1. The threshold depends on the fixed constants and A but not on Q, the selected rational or the frequency.

This checkpoint controls the explicit scalar budget. The actual minor-arc multiplier theorem still requires its displayed raw Ren and Ghosh inputs and geometric outside-arc condition; those are not hidden inside the scalar estimate. The stronger printed minor-arc formula remains open.


## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| UniformComplementaryBudget.lean | 2 |

- `complementaryMinorBudget_uniform`
- `complementaryMinorBudget_uniform_log_rate`

<!-- checkpoint-verification -->

## Verification

All 183 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 3705-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 1027 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 185 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. Published Ren and Ghosh quadratic exponential-sum estimates, when consumed, remain displayed raw theorem hypotheses; the progression-prefix estimate also remains an explicit unproved input. No own-paper analytic conclusion is assumed.

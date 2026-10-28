# Checkpoint 117: A uniform error bound on the full circle minor-arc complement

The alternative minor-arc estimate is transferred to the genuine periodized circle error. On the full all-lift complement of the source major arcs, the actual multiplier is bounded by complementaryMinorBudget, and the actual circle model by circleModelTailBudget. Their difference has norm at most the sum; no unperiodized model is substituted.

A separate uniform logarithmic bound is proved for circleModelTailBudget. Combining it with the complementary budget, the uniform source fourth-power condition and the displayed raw Ren/Ghosh inputs gives, for fixed nonnegative C,B,d and every A>=0, the bound

    norm(circle error) <= 2*2^A*Q^(-1/2)*(1+log N)^(-A).

One threshold in N works for all permitted Q, beta, character/coefficient data and frequencies on this geometric branch. The Q range is the same small-constant exp(sqrt(log N)) range as in the major-arc work. The coefficient and beta bounds, representative interval [-1,2], outside-arc condition and raw inputs are explicit. The stronger printed minor formula remains open; this alternative estimate is sufficient for the next global circle approximation assembly.


## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| UniformCircleMinorError.lean | 3 |

- `circleModelTailBudget_uniform_log_rate`
- `circleMajorArcError_minor_from_inputs`
- `circleMajorArcError_minor_uniform`

<!-- checkpoint-verification -->

## Verification

All 184 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 3706-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 1030 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 186 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. Published Ren and Ghosh quadratic exponential-sum estimates, when consumed, remain displayed raw theorem hypotheses; the progression-prefix estimate also remains an explicit unproved input. No own-paper analytic conclusion is assumed.

# Checkpoint 84: Precise kernel and symbol inputs for the actual low and high operators

The actual low operator norm is bounded by any established uniform bound on its genuine inverse kernel. The actual high l2 operator norm is bounded by any established uniform circle-symbol bound. These transport statements expose the precise analytic obligations still needed for the paper: the sharper low kernel bound and high symbol bound must be proved, not inferred merely from constructing the operators.


## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| CircleHighLowNormInputs.lean | 2 |

- `circleLowOperator_kernel_bound`
- `circleHighOperator_symbol_bound`

<!-- checkpoint-verification -->

## Verification

All 151 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 3670-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 930 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 153 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. The already displayed raw progression-prefix estimate is consumed as a theorem hypothesis; it remains unproved. No new external analytic estimate or own-paper lemma is assumed.

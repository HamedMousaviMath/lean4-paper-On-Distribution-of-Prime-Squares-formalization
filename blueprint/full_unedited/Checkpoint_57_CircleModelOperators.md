# Checkpoint 57: Actual l2 model and error operators with exact annular decomposition

The global finite circle model and its exact error define genuine bounded linear operators on integer l2 through the already checked Fourier isometry. Their sum is proved to equal the actual annular von-Mangoldt averaging operator on every l2 input. A uniform error-symbol bound is transported to the error operator norm. This is an operator-construction and transport result: it does not assume or prove the manuscript's unproved global error estimate. The exact decomposition is unconditional for the defined finite model; the small norm conclusion has its displayed pointwise hypothesis.


## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| CircleModelOperators.lean | 2 |

- `circleModel_operator_decomposition`
- `circleModel_error_operator_bound`

<!-- checkpoint-verification -->

## Verification

All 124 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 3643-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 878 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 126 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. The already displayed raw progression-prefix estimate is consumed as a theorem hypothesis; it remains unproved. No new external analytic estimate or own-paper lemma is assumed.

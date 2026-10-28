# Checkpoint 43: Source parameter budgets imply both major-arc geometric conditions

The prefix-error parameter budget also supplies the rational-arc geometry needed for the actual model comparison. For N>2, R>=1 and log N>=1, the inequality R^5 log N<=sqrt N implies both 2R^3<N^2 and 2R^4<=N^2. The proof compares R^3 and R^4 to R^5, and sqrt N to N; no asymptotic constant is hidden.

Combining this elementary deduction with the already checked source parameter threshold gives one natural-number N0, independent of Q, for both geometric conditions throughout the authorized source range log Q <= min(c/7,1)*sqrt(log N)/8. These conditions establish disjoint major arcs and force the actual smooth cutoff to equal one on the chosen major arc. The raw progression-prefix estimate and full minor-arc estimate are not established by this unit.


## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| MajorArcBudgetGeometry.lean | 2 |

- `majorArc_geometry_of_budget`
- `sourceMajorArc_uniform_geometry`

<!-- checkpoint-verification -->

## Verification

All 110 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 3629-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 850 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 112 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. The already displayed raw progression-prefix estimate is consumed as a theorem hypothesis; it remains unproved. No new external analytic estimate or own-paper lemma is assumed.

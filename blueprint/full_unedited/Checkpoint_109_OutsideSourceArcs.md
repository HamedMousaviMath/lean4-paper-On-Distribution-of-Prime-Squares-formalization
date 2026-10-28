# Checkpoint 109: Exclusion from all lifted source arcs and the effective lower bound

OutsideSourceMajorArcs is defined using the exact finite source rational set and every integer lift. It requires R/(den(r)*N^2)<=|xi+k-r| for each center and integer k. This is an explicit geometric branch condition, not a minor-arc analytic estimate.

For any rational r with den(r)<=R, the canonical-fractional-part bridge gives the same lower bound for |xi-r|. Consequently, for every rational r, the actual Ren effective denominator at x=N/2 is at least R/4: either den(r)>=R, or exclusion from its lifted small-denominator arc gives the bound. There is no restriction that the selected r already be canonical.

Finally, the existing circle-model outside-arc theorem is specialized to this exact set and all-lift condition. It bounds the genuine periodized model by circleModelTailBudget(R), including the denominator-one center and all shifted copies. The beta/coefficient bounds and representative interval [-1,2] remain explicit. No new analytic hypothesis is assumed.


## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| OutsideSourceArcs.lean | 3 |

- `outsideSourceMajorArcs_rational`
- `outsideSourceMajorArcs_effective_lower`
- `outsideSourceMajorArcs_circleModel_norm`

<!-- checkpoint-verification -->

## Verification

All 176 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 3698-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 1010 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 178 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. Published Ren and Ghosh quadratic exponential-sum estimates, when consumed, remain displayed raw theorem hypotheses; the progression-prefix estimate also remains an explicit unproved input. No own-paper analytic conclusion is assumed.

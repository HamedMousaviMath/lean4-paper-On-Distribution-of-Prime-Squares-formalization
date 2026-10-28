# Checkpoint 107: A uniform fourth-power budget for the source scale

The source-range major-arc parameter budget also controls the new complementary argument. For N>=4, R>=1, log N>=1 and R^5*log N<=sqrt(N), Lean proves R^4<=N/2. The proof retains the exact N/2 annulus: R^4<=R^5<=R^5*log N<=sqrt N<=N/2.

A real-power consequence is proved for every a>=0: if R>0 and R^4<=x, then x^(-a)<=R^(-4*a). This will convert the polynomial savings from Ren and Ghosh into powers of R without changing a fixed epsilon with N.

The final theorem supplies a single natural threshold, independent of Q, for the actual source scale R=sourceMajorArcScale(N,Q), over the same allowed Q range as the already proved progression budget. Positivity, log N>=1 and N>=4 are supplied by proved eventual limits and the existing parameter theorem. No deep estimate is added here.


## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| SourceScaleFourthPower.lean | 4 |

- `sqrt_le_half_of_four_le`
- `sourceBudget_fourth_power`
- `inverse_rpow_from_fourth_power`
- `sourceMajorArcScale_uniform_fourth_power`

<!-- checkpoint-verification -->

## Verification

All 174 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 3696-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 1004 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 176 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. Published Ren and Ghosh quadratic exponential-sum estimates, when consumed, remain displayed raw theorem hypotheses; the progression-prefix estimate also remains an explicit unproved input. No own-paper analytic conclusion is assumed.

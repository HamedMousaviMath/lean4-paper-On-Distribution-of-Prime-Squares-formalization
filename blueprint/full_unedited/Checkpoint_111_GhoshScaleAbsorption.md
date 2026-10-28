# Checkpoint 111: Converting the balanced Ghosh saving to a scale-only bound

The balanced Ghosh saving (N/2)^(-1/16) is converted to R^(-1/4) whenever R>0 and R^4<=N/2. The fixed constant B*3^(1/4)/2 is defined and proved nonnegative for B>=0.

The resulting theorem bounds the actual annular von Mangoldt circle multiplier for (N/2)^(1/2)<=q<=(N/2)^(3/2), conditional on the displayed raw Ghosh inequality at the fixed epsilon 1/16. The fourth-power hypothesis is exactly the source-scale budget proved earlier. No additional outside-arc hypothesis is needed on this balanced-denominator branch.

Ghosh's deep estimate remains a hypothesis, not an added axiom or a placeholder. The new step is the checked scale conversion and its application to the genuine multiplier, uniform in the permitted denominator.


## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GhoshScaleAbsorption.lean | 2 |

- `ghoshSourceConstant_nonneg`
- `annularMangoldt_Ghosh_scale_bound`

<!-- checkpoint-verification -->

## Verification

All 178 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 3700-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 1015 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 180 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. Published Ren and Ghosh quadratic exponential-sum estimates, when consumed, remain displayed raw theorem hypotheses; the progression-prefix estimate also remains an explicit unproved input. No own-paper analytic conclusion is assumed.

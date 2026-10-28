# Checkpoint 119: A conditional global pointwise approximation on the circle

The genuine circle error is now bounded at every representative xi in [0,1], conditional on the displayed progression-prefix, Ren and Ghosh inputs. Lean makes a complete case split over the exact finite source rational set and all integer lifts. If a lifted major arc contains xi, the wrapped conditional major theorem applies. Otherwise the logical negation supplies the outside-arc condition needed for the alternative minor theorem.

For every fixed P,C,B,d>=0, c>0 and A>=0, one natural threshold works uniformly in all permitted Q and character/coefficient/beta data, giving

    norm(actual circle error) <= 2*2^A*Q^(-1/2)*(1+log N)^(-A).

The progression estimate must hold for every source denominator and every real endpoint in [N/2,N] with the same scale data. The Ren/Ghosh inequalities are explicit pointwise hypotheses at the compatible approximants, not hypotheses asserting the desired error conclusion. There is no gap between the two cases and no assumption of the paper's own minor-arc or approximation lemma.

This completes the conditional global pointwise analytic deduction for the genuine circle model. The next steps extend the bound to every circle point and to the actual bounded l2 operator. The stronger printed Lemma 6.5, full exceptional-data/source correspondence and sharp low/high/maximal inputs remain open; Theorem 1.1 is not proved.


## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GlobalCircleApproximation.lean | 1 |

- `globalCircleApproximation_uniform`

<!-- checkpoint-verification -->

## Verification

All 186 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 3708-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 1033 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 188 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. Published Ren and Ghosh quadratic exponential-sum estimates, when consumed, remain displayed raw theorem hypotheses; the progression-prefix estimate also remains an explicit unproved input. No own-paper analytic conclusion is assumed.

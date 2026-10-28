# Checkpoint 113: An alternative full-range minor-arc deduction under raw deep estimates

This checkpoint completes an alternative full-range minor-arc deduction for the actual annular von Mangoldt circle multiplier, conditional on displayed raw Ren and Ghosh estimates. The two input predicates state precise inequalities for the actual sum at compatible rational approximations. They are propositions in theorem hypotheses, not mathematical axioms.

Lean selects a reduced rational at precision x^(-3/2), x=N/2, using the proved existence theorem. If its denominator is at most sqrt(x), the all-lift outside-source-arc condition supplies the lower effective-denominator bound and the Ren branch applies. If its denominator exceeds sqrt(x), it lies in the proved balanced Ghosh range and satisfies the strict reciprocal-square approximation condition. There is no uncovered denominator range.

For N>=4, R>=1 and R^4<=N/2, the result is

    norm(actual annular multiplier) <= renSourceConstant(C)*(log(N/2))^c*R^(-5/12)
                                      + ghoshSourceConstant(B)*R^(-1/4).

The combined budget is proved nonnegative. The fixed epsilon in Ghosh is 1/16; the divisor-growth epsilon is fixed at 1/12. Neither depends on N. The estimate is valid on the full complement of the small-denominator lifted major arcs and does not rely on the manuscript's original approximant. It is weaker than the stronger printed minor-arc formula in Lemma 6.5, which remains open; it is intended to suffice for global approximation Lemma 6.9. No manuscript replacement is prescribed on this basis.


## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| ComplementaryMinorArcBound.lean | 2 |

- `complementaryMinorBudget_nonneg`
- `annularMangoldt_complementary_minor_bound`

<!-- checkpoint-verification -->

## Verification

All 180 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 3702-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 1019 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 182 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. Published Ren and Ghosh quadratic exponential-sum estimates, when consumed, remain displayed raw theorem hypotheses; the progression-prefix estimate also remains an explicit unproved input. No own-paper analytic conclusion is assumed.

# Checkpoint 94: Exact periodization and logarithmic circle-model tails

The genuine periodization is reduced exactly to the five integer shifts -2,-1,0,1,2 for every canonical rational center and every real representative xi in [-1,2]. The centered cutoff model vanishes at distance at least one; this proves that all omitted shifts are zero, including the boundary cases. Summing over the rational centers and interchanging the finite sums gives the exact same representation for the actual continuous circle model.

If a representative is outside every small major arc at each of those five shifts, the actual circle model has norm at most

    T_circle(R) = 5*(5+log(R)/log(2))*(4*C_G/pi)*R^(-5/12),

where C_G is the positive constant chosen from the previously proved, unconditional ordinary/exceptional Gauss-model bounds. This is a logarithmic tail estimate, rather than the much larger sum of absolute coefficient bounds over all denominators. All cutoffs and actual integral models retain their existing definitions.

A common approximation budget is defined by

    B(C,R) = (4+(2+4*pi)*C)/R^5 + C_G*R^(-5/12) + T_circle(R).

Lean proves that T_circle(R)<=R^(-1/3) eventually and B(C,R)<=R^(-1/6) eventually for every fixed C>=0. Substituting the actual source scale R=max(exp((log N)^(1/10)),Q^8) gives, for every A>=0, a threshold in N independent of Q>=1 with B(C,R)<=2^A*Q^(-1/2)*(1+log N)^(-A).

This checkpoint bounds the model and its explicit error budget. It does not prove that the prime-square multiplier is close to that model at all frequencies. No distribution hypothesis is consumed by these statements. The actual approximation branches are treated in the subsequent checkpoints; the full-range minor-arc problem remains open.


## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| PeriodizedModelTails.lean | 8 |

- `fivePeriodShifts_card`
- `integerPeriodSum_five`
- `circleRationalModelTerm_five`
- `circleMajorArcModel_five`
- `circleMajorArcModel_outside_norm`
- `eventually_circleModelTailBudget`
- `eventually_circleApproxBudget`
- `circleApproxBudget_uniform_log_rate`

<!-- checkpoint-verification -->

## Verification

All 161 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 3680-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 961 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 163 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. The already displayed raw progression-prefix estimate is consumed as a theorem hypothesis; it remains unproved. No new external analytic estimate or own-paper lemma is assumed.

# Checkpoint 96: Intermediate-denominator approximation for the genuine circle model

This checkpoint proves the intermediate-denominator part of the actual circle approximation. Suppose a reduced rational r=a/q approximates the chosen real representative with |xi-r|<=R/(q*N^2), and

    R < q <= R^(11/10).

The already proved inverse-fifth progression estimate controls the difference between the actual annular von Mangoldt multiplier and its genuine Gauss model. The unconditional Gauss bounds give model size at most C_G*q^(-5/12), which is at most C_G*R^(-5/12). Lean therefore proves a bound for the actual multiplier by (4+(2+4*pi)*C)/R^5+C_G*R^(-5/12).

On the branch outside all small-denominator major arcs, including all integer lifts relevant for the representative in [-1,2], checkpoint 94 bounds the actual circle model by circleModelTailBudget(R). Subtracting it gives the same circleApproxBudget(C,R) used on the major-arc branch. The outside-arc assumption is an explicit geometric case condition, not an assumed minor-arc estimate. The approximating rational need not itself belong to the small-denominator set.

The uniform theorem specializes to the exact source rational set and source scale. For C>=0, c>0 and A>=0, one threshold in N, independent of Q and the permitted data, gives the bound 2^A*Q^(-1/2)*(1+log N)^(-A) whenever Q>=1, log Q <= (min(c/7,1)/8)*sqrt(log N), and the displayed raw progression-prefix inequality holds at the approximating denominator throughout [N/2,N]. This is the same kind of explicit deep input already used in the preceding source-range major-arc work; no new analytic axiom is introduced.

The major-arc and intermediate branches now refer to the genuine periodized circle model, with precise finite rational indexing and all integer shifts accounted for. The existence/selection of an appropriate rational approximation is not asserted by this checkpoint. The branch q>R^(11/10), including the unresolved full-range minor-arc deduction, remains open. Consequently full Lemma 6.5, global Lemma 6.9, sharp low 6.14, multifrequency 6.16, high/maximal 6.21, Proposition 4.19 and Theorem 1.1 remain unproved. The full exceptional-parameter/source correspondence also remains open. No new manuscript correction has been established.


## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| IntermediateCircleApproximation.lean | 3 |

- `annularMangoldt_intermediate_norm`
- `circleMajorArcError_intermediate_from_prefix`
- `circleMajorArcError_intermediate_uniform_log_rate`

<!-- checkpoint-verification -->

## Verification

All 163 project modules and the root were freshly rebuilt: 3682 jobs pass without warnings/errors. All 968 named theorems pass the complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound. The source scan checks 165 Lean files. Exact unique import/audit coverage and unchanged frozen source hashes are checked before packaging. There are no placeholders or added mathematical axioms.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. The already displayed raw progression-prefix estimate is consumed as a theorem hypothesis; it remains unproved. No new external analytic estimate or own-paper lemma is assumed.

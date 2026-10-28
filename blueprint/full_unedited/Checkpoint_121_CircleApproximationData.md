# Checkpoint 121: A conditional global approximation for the actual l2 operator

The explicit deep analytic inputs are collected in CircleAnalyticInputs: 0<beta<=1, coefficient norms at most one, the actual raw progression-prefix inequality for every source rational denominator and every real endpoint in [N/2,N], and the compatible raw Ren/Ghosh inequalities for every representative xi in [0,1]. The structure contains no approximation, operator-norm or own-paper lemma conclusion.

From these inputs, Lean proves a bound for the actual circle error at every circle point. It then proves the norm bound for the genuine l2 error operator, with one N threshold before all permitted Q and input data:

    norm(error operator) <= 2*2^A*Q^(-1/2)*(1+log N)^(-A).

This is an end-to-end conditional analytic deduction for the periodized approximation: exact finite rational indexing, compatible rational selection, both major and alternative minor branches, all integer lifts, the circle representative bridge and the actual Fourier operator are included. The deep number-theory inputs remain hypotheses, as authorized, rather than added axioms or placeholders.

The stronger printed minor estimate of Lemma 6.5 has not been established, and the full source exceptional-parameter and double-sum correspondence is not silently certified by the input structure. Sharp low/high/multifrequency/maximal estimates and Theorem 1.1 remain open. This checkpoint performs a fresh full project rebuild and complete axiom/source audits before packaging.


## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| CircleApproximationData.lean | 2 |

- `globalCircleApproximation_all_points`
- `globalCircleApproximation_l2_operator`

<!-- checkpoint-verification -->

## Verification

All 188 project modules and the root were freshly rebuilt: 3710 jobs pass without warnings/errors. All 1038 named theorems pass the complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound. The source scan checks 190 Lean files. Exact unique import/audit coverage and unchanged frozen source hashes are checked before packaging. There are no placeholders or added mathematical axioms.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. Published Ren and Ghosh quadratic exponential-sum estimates, when consumed, remain displayed raw theorem hypotheses; the progression-prefix estimate also remains an explicit unproved input. No own-paper analytic conclusion is assumed.

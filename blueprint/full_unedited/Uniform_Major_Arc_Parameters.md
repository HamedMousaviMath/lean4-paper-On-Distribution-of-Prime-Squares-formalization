# Uniform parameter inequalities for the source major-arc scale

Checkpoint 29. This unit proves the elementary asymptotic parameter
conditions needed for the inverse-fifth major-arc bound. It has no
prime-distribution hypothesis and introduces no deep analytic input.

Define the actual source scale, for real N,Q, by

\[
 R(N,Q)=\max\{\exp((\log N)^{1/10}),Q^8\}.
\]

The Lean definition is `sourceMajorArcScale`. It is positive everywhere,
and at least one when N>=1. In applications N is a positive integer.

## Uniformity in Q

For any fixed epsilon>0, real powers satisfy

\[
 x^{1/10}=o(x^{1/2})\quad(x\longrightarrow\infty).
\]

The supporting theorem `eventually_rpow_le_mul_rpow` proves the general
comparison x^a<=epsilon*x^b eventually when a<b. Its proof uses the
checked limit of x^(a-b) to zero and division by the positive x^b.
Composition with log(N) tending to infinity gives the comparison needed
for the first term in R.

If log(Q)<=(epsilon/8)*sqrt(log N), then Q^8<=exp(epsilon*sqrt(log N)).
Both terms defining the maximum therefore satisfy the same upper bound.
Taking logarithms proves, for all sufficiently large N and every Q>=1,

\[
 \log Q\leq\frac\epsilon8\sqrt{\log N}
 \quad\Longrightarrow\quad
 \log R(N,Q)\leq\epsilon\sqrt{\log N}.
\]

The threshold depends on epsilon alone, not on Q. This is the quantified
statement `eventually_sourceMajorArcScale_log_upper`.

## The nonunit budget

For any fixed epsilon>0, eventually

\[
 \epsilon\sqrt{\log N}\leq\frac{\log N}{20},\qquad
 \log N\leq\exp((\log N)/4).
\]

The first follows from the same power comparison; the second follows
from Mathlib's proved domination of powers by the exponential. Thus,
whenever R>0 and log(R)<=epsilon*sqrt(log N),

\[
 \log R\leq\log N,\qquad
 R^5\leq\exp((\log N)/4),\qquad
 R^5\log N\leq\exp((\log N)/2)=\sqrt N.
\]

`eventually_majorArc_nonunit_conditions` proves both required conditions
uniformly for every such R. No unspecified eventual bound is supplied as
a hypothesis: the proof establishes its existence from checked limits.

## An explicit admissible coefficient

Given any positive decay constant c, take

\[
 \epsilon=\min\{c/7,1\},\qquad c_0=\epsilon/8>0.
\]

For all sufficiently large N, simultaneously for every Q>=1 with
log(Q)<=c_0*sqrt(log N), the actual source R satisfies

\[
 R\geq1,\quad \log R\leq\log N,\quad
 R^5\log N\leq\sqrt N,\quad 7\log R\leq c\sqrt{\log N}.
\]

This is `eventually_sourceMajorArc_conditions`. These are precisely the
elementary inequalities used in checkpoint 28. This choice controls the
error absorption; applicability of an external progression theorem in
its own modulus range remains a separate condition on that external
input. No existence or range of an exceptional zero is asserted here.

The next unit transfers this real-variable eventual statement to
integer N and connects it to the actual ordinary and exceptional
major-arc bounds. Full Lemma 6.5 and Theorem 1.1 remain open.

| Module | New named theorems | Result |
|---|---:|---|
| MajorArcParameters.lean | 8 | Actual source scale, positive and exponential/logarithmic bounds, proved power comparison and uniform eventual parameter conditions |

All statements in this unit are unconditional elementary analysis.

<!-- checkpoint-verification -->

## Verification

All 93 project modules and the root were freshly rebuilt: 3608 jobs pass without warnings/errors. All 757 named theorems pass the complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound. The source scan checks 95 Lean files. Exact unique import/audit coverage and unchanged frozen source hashes are checked before packaging. There are no placeholders or added mathematical axioms.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. No new deep analytic input or own-paper lemma is assumed.

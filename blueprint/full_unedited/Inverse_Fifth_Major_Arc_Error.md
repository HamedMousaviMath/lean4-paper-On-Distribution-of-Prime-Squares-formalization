# Explicit absorption into the inverse fifth power of R

Checkpoint 28. This unit proves the R^-5 major-arc error from the
previous explicit error budget, under three displayed numerical
conditions. The next unit establishes these conditions uniformly for the
manuscript's choice of R. The raw progression estimate remains a hypothesis.

Assume N>=1, R>=1, C>=0 and an actual progression-prefix error bounded
throughout [N/2,N] by

\[
 N C\exp(-c\sqrt{\log N}).
\]

The same beta>0 and character data must be used over that interval. The
major-arc range is q<=R^(11/10), abs(theta)<=R/(q*N^2).

## Exponential absorption

For R>0, the condition 7*log(R)<=t implies

\[
 R^2e^{-t}=\exp(2\log R-t)
 \leq\exp(-5\log R)=R^{-5}.
\]

`exponential_majorArc_absorption` proves this for every real t. In the
application t=c*sqrt(log N). There is no unspecified loss in its constant.

## The nonunit contribution

Suppose additionally

\[
 \log R\leq\log N,\qquad R^5\log N\leq\sqrt N.
\]

Since sqrt(N)<=N for N>=1, these hypotheses give
R^5*log(R)<=N and R^5*sqrt(N)*log(N)<=N. Multiplying the nonunit
budget by the positive R^5 and N therefore proves

\[
 \frac{2\log R+2\sqrt N\log N}{N}\leq\frac4{R^5}.
\]

The exact square-root identity, positivity of N, and every denominator
cancellation are checked in `nonunit_majorArc_absorption`.

## Bound for the actual symbol

Combining the two calculations with checkpoint 27 proves

\[
 \begin{aligned}
 \big|\widehat{\widetilde A}_{N,\Lambda}(a/q+\theta)
 &-\big(\mathfrak s(a,q)M_{N,1}(\theta)
       -\mathfrak s_\chi(a,q)\kappa M_{N,\beta}(\theta)\big)\big|\\
 &\leq\frac{4+(2+4\pi)C}{R^5},
 \end{aligned}
\]

provided the three displayed conditions hold, including
7*log(R)<=c*sqrt(log N). This is
`annularMangoldt_majorArc_inverse_fifth`. It is a theorem about the
genuine annular Fourier sum, including all von Mangoldt prime powers.
The constant depends only on the raw prefix-error constant C.

This proves the conditional inverse-fifth deduction with finite,
checkable parameter hypotheses. It does not yet remove those numerical
hypotheses for the source's N,Q range, prove existence of the analytic
prefix estimate, or establish the independent minor-arc bound. Full
Lemma 6.5, Proposition 4.19 and Theorem 1.1 remain open.

| Module | New named theorems | Result |
|---|---:|---|
| ExponentialMajorArcBudget.lean | 4 | Exponential absorption, nonunit absorption, combined error and the actual conditional inverse-fifth major-arc theorem |

No new deep theorem is assumed in this unit, and no numerical experiment
is used as a substitute for these Lean proofs.

<!-- checkpoint-verification -->

## Verification

All 92 project modules and the root were freshly rebuilt: 3607 jobs pass without warnings/errors. All 749 named theorems pass the complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound. The source scan checks 94 Lean files. Exact unique import/audit coverage and unchanged frozen source hashes are checked before packaging. There are no placeholders or added mathematical axioms.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. No new deep analytic input or own-paper lemma is assumed.

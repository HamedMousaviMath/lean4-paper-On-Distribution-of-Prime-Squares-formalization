# The uniform source-range major-arc implication

Checkpoint 30. The finite Fourier reduction, actual partial summation,
error absorption and source parameter inequalities are now assembled.
The major-arc R^-5 implication is proved in the source N,Q range,
conditional on the displayed genuine progression-prefix estimate.

## Quantified statement

Fix c>0 and put c0=min(c/7,1)/8. There is an integer N0>=1 depending
on c alone such that the following holds for every integer N>=N0 and
every real Q>=1 satisfying

\[
 \log Q\leq c_0\sqrt{\log N}.
\]

Let R=max(exp((log N)^(1/10)),Q^8). For every positive modulus q,
complex Dirichlet character chi modulo q, coefficient kappa, beta>0,
integer a and real theta, suppose

\[
 q\leq R^{11/10},\qquad |\theta|\leq R/(qN^2).
\]

Suppose C>=0 and the actual progression prefix satisfies

\[
 \left|C_{q,u}(t)-\frac1{\phi(q)}
     \left(t-\kappa\chi(u)\frac{t^\beta}{\beta}\right)\right|
 \leq NC\exp(-c\sqrt{\log N})
 \quad(N/2\leq t\leq N)
\]

for every reduced residue u. Then

\[
 \begin{aligned}
 \big|\widehat{\widetilde A}_{N,\Lambda}(a/q+\theta)
 &-\big(\mathfrak s(a,q)M_{N,1}(\theta)
       -\mathfrak s_\chi(a,q)\kappa M_{N,\beta}(\theta)\big)\big|\\
 &\leq\frac{4+(2+4\pi)C}{R^5}.
 \end{aligned}
\]

`sourceMajorArc_uniform_inverse_fifth` proves exactly this implication.
Its N0 is chosen before Q,q,chi,kappa,beta,a,theta and C. Thus the
threshold is uniform over the displayed range; the error constant depends
only on C. It applies in particular to the source's dyadic N and Q>=2.

## Assembly of the proof

`sourceMajorArc_parameter_threshold` composes the proved real-variable
eventual parameter conditions with the divergence of the natural numbers
in the reals. It chooses a natural threshold at least one. For N>=N0,
the actual R therefore satisfies R>=1, log(R)<=log(N),
R^5*log(N)<=sqrt(N), and 7*log(R)<=c*sqrt(log(N)).

The fixed-parameter actual-symbol theorem from checkpoint 28 then applies
directly. Every integration-by-parts, integrability, finite Gauss-sum and
normalization condition has already been discharged. None is reinstated
as an assumption in the final theorem.

`sourceMajorArc_uniform_ordinary` gives the separate ordinary statement
from a raw prefix estimate around t/phi(q), with no exceptional parameter
in its conclusion. Its proof specializes kappa=0 and uses the proved
identity for the zero exceptional model. In the exceptional application
kappa=1 includes the correction. Data can change between scales N; at
each one scale the same data must work throughout [N/2,N].

## Exact trust boundary

The raw exponential progression-prefix inequality above is still a theorem
hypothesis. This unit does not construct exceptional characters or zeros,
prove a Page/Siegel-Walfisz theorem, or assert that an unverified version
of a published theorem supplies the hypothesis. Its applicability in the
external theorem's own modulus range must be checked separately. The
explicit c0 above controls the elementary error absorption.

The major-arc part of Lemma 6.5 is now a verified implication from this
raw analytic input in the source range. The independent minor-arc bound
has not been established over its full stated range, so full Lemma 6.5
remains open. The next unit handles the exact Ren input and its genuinely
proved deduction. Proposition 4.19 and Theorem 1.1 remain later targets;
Theorem 1.1 is not counted as formalized.

| Module | New named theorems | Result |
|---|---:|---|
| SourceRangeMajorArc.lean | 3 | Uniform integer parameter threshold and actual exceptional/ordinary source-range inverse-fifth major-arc implications |

No new mathematical axiom or numerical experiment is used.

<!-- checkpoint-verification -->

## Verification

All 94 project modules and the root were freshly rebuilt: 3609 jobs pass without warnings/errors. All 760 named theorems pass the complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound. The source scan checks 96 Lean files. Exact unique import/audit coverage and unchanged frozen source hashes are checked before packaging. There are no placeholders or added mathematical axioms.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. No new deep analytic input or own-paper lemma is assumed.

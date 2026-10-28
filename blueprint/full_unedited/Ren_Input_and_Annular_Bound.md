# Ren's actual annular sum and a verified minor-arc consequence

Checkpoint 31. This unit connects the paper's genuine negative-phase
annular Fourier sum to Ren's positive-phase sum, transports the exact
three-term bound, and proves a valid decay consequence in an explicit
parameter range. It leaves the manuscript's wider minor-arc claim open.

## Published input and its scope

The primary text inspected is Xiumin Ren's author preprint,
[On exponential sum over primes and application in Waring-Goldbach
problem](https://www.math.hku.hk/imrwww/IMRPreprintSeries/2004/IMR2004-9.pdf),
Theorem 1.1, corresponding to the cited 2005 paper. Its sum is already
over x<m<=2x. For k=2, frequency xi=a/q+theta and reduced a/q, its
displayed bound has the form

\[
 |S(x,\xi)|\leq C\tau(q)^{3/2}(\log x)^A
 \left(\sqrt{x}\sqrt{T}+x^{4/5}+\frac{x}{\sqrt T}\right),
 \qquad T=q(1+|\theta|x^2).
\]

Here C,A are fixed constants supplied by the analytic result. The exact
journal text was not accessible; the author-hosted preprint's statement
and first-page formula were checked. This result itself is not proved in
Lean or added as an axiom. The consuming theorems display the actual
inequality as a hypothesis. External applicability requires x in the
theorem's large-parameter range and the stated rational approximation.

## Actual sum, sign and endpoints

`renQuadraticSum` is the complex finite sum of Lambda(n)*e(xi*n^2)
over floor(x)<n<=floor(2x). `renQuadraticSum_exp` identifies the exact
positive complex exponential explicitly. Conjugation of this actual sum
reverses the sign of xi and preserves its norm, because Lambda is real.
These are proved identities, not assumed Fourier conventions.

Taking x=N/2 uses the real lower endpoint, with floor(N/2)=N/2 in natural
division and floor(2*(N/2))=N. Thus for every natural N,

\[
 \widehat{\widetilde A}_{N,\Lambda}(\xi)
 =\frac1N S(N/2,-\xi),\qquad
 \left|\widehat{\widetilde A}_{N,\Lambda}(\xi)\right|
 =\frac1N |S(N/2,\xi)|.
\]

These identities even handle odd N and the inverse convention at N=0.
Applying the external analytic theorem requires N sufficiently large;
the explicit source-prefactor corollary below uses N>=4. No prime powers
are dropped. There is no need to reconstruct this annular sum by
subtracting two initial sums.

## Exact bound transported to the annulus

Put B=C*tau(q)^(3/2)*(log x)^A and

\[
 J(x,T)=\sqrt{x}\sqrt T+x^{4/5}+x/\sqrt T.
\]

`annularMangoldt_from_Ren_bound` proves directly from the raw inequality
|S(N/2,xi)|<=B*J(N/2,T) that

\[
 \left|\widehat{\widetilde A}_{N,\Lambda}(\xi)\right|
 \leq \frac{B}{N}J(N/2,T).
\]

This retains all three terms and every normalizing factor. The theorem
does not assert that arbitrary independent choices of xi,theta,q satisfy
the analytic input: the genuine raw inequality is displayed.

## A proved decay range

For x>0, R>0, assume

\[
 R\leq T\leq x/R,\qquad R\leq x^{2/5}.
\]

Then each term of J(x,T) is at most x/sqrt(R). Indeed:

1. T*R<=x implies sqrt(T)*sqrt(R)<=sqrt(x), and hence
   sqrt(x)*sqrt(T)<=x/sqrt(R).
2. R<=x^(2/5) implies sqrt(R)<=x^(1/5), giving
   x^(4/5)*sqrt(R)<=x.
3. T>=R implies x/sqrt(T)<=x/sqrt(R).

Thus `ren_bracket_central_bound` proves J(x,T)<=3*x/sqrt(R). The exact
N=2x normalization gives

\[
 \left|\widehat{\widetilde A}_{N,\Lambda}(\xi)\right|
 \leq\frac{3B}{2\sqrt R}.
\]

`annularMangoldt_Ren_central_source` substitutes the actual divisor and
logarithmic prefactor and T=q*(1+abs(theta)*(N/2)^2). Its positivity is
proved using N>=4 and C>=0. The divisor factor multiplies the whole
bound; it has not been discarded or silently absorbed into a logarithm.

## The remaining source deduction

The manuscript's Lemma 6.5 asks for a minor-arc estimate throughout
R^(11/10)<q<=N^2/R with abs(theta)<=R/(q*N^2). Those conditions do not
imply the central-range hypothesis T<=x/R. For example, theta=0 and
q comparable to N give T comparable to x. At T=x, the first normalized
term in Ren's displayed estimate is exactly

\[
 \frac{\sqrt x\sqrt T}{x}=1.
\]

`ren_first_term_diagonal` proves this identity for every x>0. Thus direct
substitution into this particular bound does not supply a decaying estimate
in the entire source range. A further argument or a complementary estimate
must be supplied and checked. This is a gap in the currently verified
deduction, not a counterexample to the manuscript's minor-arc assertion.
No replacement of that assertion is prescribed on this evidence alone.

The conditional source-range major-arc R^-5 theorem remains intact. Full
Lemma 6.5 stays open pending its independent full-range minor-arc argument
and the precise external-input bridge. Proposition 4.19 and the paper's
Theorem 1.1 remain explicit later targets.

| Module | New named theorems | Result |
|---|---:|---|
| RenSumCompatibility.lean | 6 | Positive-phase exponential, conjugation, exact floor endpoints and actual annular normalization |
| RenMinorArcBound.lean | 5 | Raw Ren bound transport, proved central-range decay with actual prefactor, and the diagonal diagnostic |

All new deductions are Lean proofs. Ren's deep estimate is a displayed
theorem hypothesis, with no new mathematical axiom or proof placeholder.

<!-- checkpoint-verification -->

## Verification

All 96 project modules and the root were freshly rebuilt: 3611 jobs pass without warnings/errors. All 771 named theorems pass the complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound. The source scan checks 98 Lean files. Exact unique import/audit coverage and unchanged frozen source hashes are checked before packaging. There are no placeholders or added mathematical axioms.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. Ren's displayed three-term estimate enters only as an explicit hypothesis of conditional consuming theorems; it is not added as an axiom. No own-paper lemma is assumed.

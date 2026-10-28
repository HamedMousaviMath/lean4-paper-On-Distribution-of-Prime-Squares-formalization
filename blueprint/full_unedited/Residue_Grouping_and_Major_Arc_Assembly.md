# Residue grouping and finite major-arc assembly

Checkpoint 23. Source: Draft5, proof of Lemma 6.5
(`l:prime-square-input`), immediately after `e:prime-square-minor-input`.
This unit proves the finite residue decomposition, controls the discarded
non-unit terms, and assembles the ordinary and twisted Gauss factors with
explicit error accounting. The full major-arc and minor-arc statements of
Lemma 6.5 remain open.

## Actual sums and conventions

For finite S contained in {1,...,N}, real c and real weights w, the
already constructed continuous Fourier symbol is

\[
 m_{S,c,w}(\xi)=c\sum_{n\in S}w(n)e(-n^2\xi).
\]

The actual annular von Mangoldt symbol takes S = {floor(N/2)+1,...,N},
c = 1/N and w(n) = Lambda(n), including every prime power. Frequencies
are in the period-one additive circle. Finite regrouping works for every
positive modulus q and every integer numerator a; no coprimality or
major-arc size restriction is needed for these algebraic identities.

Define the unnormalized residue sum

\[
 W_r(\theta)=\sum_{\substack{n\in S\\n\equiv r\pmod q}}
                  w(n)e(-n^2\theta).
\]

This is `squareResidueSum`. It is a finite sum using the actual equality
of natural-number casts in ZMod q. The normalization c is kept outside
W_r, so it cannot be silently applied twice.

## Non-unit support and its sharper elementary bound

If Lambda(n) is nonzero, Mathlib's actual von Mangoldt definition implies
n = p^k for some prime p and k >= 1. If n is not coprime to q, then p
must divide q: otherwise p is coprime to q, hence so is p^k.
`mangoldt_nonunit_prime_power` proves this support statement.

Split the non-unit mass into primes and non-primes. For the prime part,
only distinct primes dividing q can occur. Therefore

\[
 \sum_{\substack{n\in S\\n\text{ prime}\\(n,q)>1}}\Lambda(n)
 \leq\sum_{p\mid q}\log p\leq\log q,\qquad q>0.
\]

The last inequality is the already proved `primeFactors_log_budget`:
the product of the distinct primes dividing q divides q. The finite-set
inclusion and the use of the actual prime value Lambda(p)=log(p) are
proved in `mangoldt_prime_nonunit_mass_le_log`.

For all the non-prime terms, including those coprime to q, the pinned
Mathlib identifies the full weighted mass with psi(N)-theta(N), then
proves the elementary estimate

\[
 0\leq\psi(N)-\vartheta(N)\leq2\sqrt N\log N,\qquad N\geq1.
\]

The exact declarations are `Chebyshev.psi_sub_theta_eq_sum_not_prime`
and `Chebyshev.psi_sub_theta_le`. By nonnegativity of Lambda, any subset
of the higher prime powers has at most this mass. Our
`mangoldt_nonprime_mass_bound` proves that subset implication.

Combining the two parts gives, for every S contained in {1,...,N},

\[
 0\leq\sum_{\substack{n\in S\\(n,q)>1}}\Lambda(n)
 \leq\log q+2\sqrt N\log N.
\]

This is `mangoldtNonunitMass_le`. N >= 1 and q > 0 are its only size
restrictions. For q=1 the discarded set is actually empty;
`mangoldtNonunitMass_one` records exact vanishing.

The source uses the looser normalized error
O(N^(-1/2)(log N)^2 + q N^(-1)(log N)^2). The proved explicit estimate
above is sharper and is sufficient for this reduction step. It does not
require changing the source statement. No PNT or distribution-in-
progressions estimate is used; the Chebyshev bound is already proved
in the same pinned Mathlib.

## The exact residue identity

For every integer n and circle offsets alpha,beta, the negative Fourier
character obeys c_n(alpha+beta)=c_n(alpha)c_n(beta). At a rational frequency
we already know c_(n^2)(a/q)=stdAddChar_q(-a*n^2). We prove and apply the
argument-addition identity, obtaining

\[
 e(-n^2(a/q+\theta))
 =e(-a n^2/q)e(-n^2\theta).
\]

Within the class n congruent to r modulo q, the first factor is exactly
e(-a r^2/q). Each natural n lies in one and only one residue class, so
finite interchange of summation gives

\[
 m_{S,c,w}(a/q+\theta)
 =c\sum_{r\in\mathbb Z/q\mathbb Z}e(-a r^2/q)W_r(\theta).
\]

`finite_sum_residue_fibers` proves the partition identity and
`finiteSquareSymbol_residues` applies the actual rational phase.

A natural-number cast is a unit in ZMod q exactly when it is coprime to q.
This proves that restricting S to the coprime n retains W_r precisely for
unit r and makes it zero for other r. The earlier exact equivalence between
the unit-filter convention and the actual unit group then gives

\[
 m_{S,c,w}(a/q+\theta)
 =c\sum_{r\in(\mathbb Z/q\mathbb Z)^\times}e(-a r^2/q)W_r(\theta)
   +\mathcal E_{\mathrm{nonunit}},
\]

where the remainder is explicitly

\[
 \mathcal E_{\mathrm{nonunit}}
 =c\sum_{\substack{n\in S\\(n,q)>1}}w(n)e(-n^2(a/q+\theta)).
\]

This is `finiteSquareSymbol_reduced_residues`. It retains an equality
with an actual finite remainder, rather than replacing the remainder by
an unexplained big-O term.

For nonnegative c and weights, the triangle inequality and unit magnitude
of every Fourier character give

\[
 |m_{S,c,w}(\xi)|\leq c\sum_{n\in S}w(n).
\]

Together with the mass estimate, this proves, for the actual annular
Lambda symbol and N >= 1,

\[
 \left|\widehat{\widetilde A}_{N,\Lambda}(a/q+\theta)
 -\frac1N\sum_{r\in(\mathbb Z/q\mathbb Z)^\times}e(-ar^2/q)W_r(\theta)\right|
 \leq\frac{\log q+2\sqrt N\log N}{N}.
\]

`annularMangoldt_reduced_residues_bound` is this unbounded, uniform-in-
frequency Lean theorem. Its q=1 remainder is exactly zero. The finite
identities also cover empty S and the total N=0 definition; the logarithmic
inequality is stated only for N >= 1.

## Ordinary and twisted Gauss assembly

Fix q>0, an arbitrary complex Dirichlet character chi modulo q, and two
complex numbers M_1 and M_beta. In a future application these will be the
ordinary and exceptional oscillatory integrals. No assertion about those
integrals or a progression asymptotic is assumed in this unit.

For each residue r define its actual normalized model error by

\[
 \varepsilon_r=c W_r(\theta)
 -\frac1{\varphi(q)}\bigl(M_1-\chi(r)M_\beta\bigr).
\]

The function `squareResidueModelError` is exactly this difference. In the
Lean declaration the scalar names are `M,E`; they denote M_1,M_beta here.
That scalar E is separate from both the non-unit remainder and the
paper's global error operator E_(Q,N).

The Section 3 Gauss definitions have already fixed

\[
 \mathfrak s(a,q)=\frac1{\varphi(q)}\sum_{r\in(\mathbb Z/q\mathbb Z)^\times}e(-ar^2/q),
 \quad
 \mathfrak s_\chi(a,q)=\frac1{\varphi(q)}
   \sum_{r\in(\mathbb Z/q\mathbb Z)^\times}\chi(r)e(-ar^2/q).
\]

Distributivity of these actual finite sums gives

\[
 \sum_r e(-ar^2/q)\frac{M_1-\chi(r)M_\beta}{\varphi(q)}
 =\mathfrak s(a,q)M_1-\mathfrak s_\chi(a,q)M_\beta.
\]

This is `unitSquareGauss_model_identity`. Combining it with the exact
residue decomposition and the definition of epsilon gives the identity

\[
 m_{S,c,w}(a/q+\theta)
 -\bigl(\mathfrak s(a,q)M_1-\mathfrak s_\chi(a,q)M_\beta\bigr)
 =\mathcal E_{\mathrm{nonunit}}+\sum_r e(-ar^2/q)\varepsilon_r.
\]

`finiteSquareSymbol_majorArc_error_identity` proves this formula for all
of the displayed data, without an approximation hypothesis. It preserves
the exceptional minus sign and the exact totient normalization.

Taking norms gives the sum of the actual residue-error norms. For the
annular Lambda average this is

\[
 \left|\widehat{\widetilde A}_{N,\Lambda}(a/q+\theta)
 -\bigl(\mathfrak s(a,q)M_1-\mathfrak s_\chi(a,q)M_\beta\bigr)\right|
 \leq\frac{\log q+2\sqrt N\log N}{N}+\sum_r|\varepsilon_r|.
\]

If a later argument proves |epsilon_r| <= delta on every unit residue,
there are exactly phi(q) such residues. The final theorem therefore gives

\[
 \text{error}\leq\frac{\log q+2\sqrt N\log N}{N}+\varphi(q)\delta.
\]

The per-residue bound is an explicit hypothesis of this last implication;
it has not been established by naming the errors. The preceding identity
and sum-of-errors inequality have no such hypothesis. Without an
exceptional contribution one can put M_beta=0. All assertions are at an
individual scale, and do not freeze exceptional data as N varies.

## Files and proof scope

| Module | New named theorems | Completed work |
|---|---:|---|
| MangoldtNonunits.lean | 6 | Actual non-unit prime-power support and logarithmic/Chebyshev mass bound |
| SquareResidueGrouping.lean | 8 | Exact rational shift, full residue partition and unit-group decomposition |
| MangoldtResidueReduction.lean | 4 | Uniform explicit remainder for the actual annular Lambda symbol |
| SquareMajorArcAssembly.lean | 5 | Exact ordinary/twisted Gauss assembly and finite error accounting |

These are 23 supporting theorems. They complete these finite proof steps,
not either full numbered conclusion of Lemma 6.5. The ten completed
numbered paper results are unchanged. No own-paper lemma or new deep
analytic input has been assumed.

The full fresh artifact-cache-disabled build passes 3599 jobs, with all
84 modules and the root rebuilt and no warnings/errors. All 701 named
project theorems pass the complete transitive whitelist: propext,
Classical.choice and Quot.sound. The source scan checks 86 Lean files;
there are no placeholders or added mathematical axioms. No dependency
version was changed and no new Mathlib cache target was required.

## Independent finite checks

`scripts/check_residue_grouping.py` checks 18144 finite residue identities
and 18144 corresponding Gauss/error identities. It uses q=1,...,12,
N=0,...,8, full and annular windows, ordinary/Lambda/signed weights,
negative and positive numerators, offsets 0,1/2,-1/3,1/4, and principal
or available induced real characters. Both a nonzero exceptional model
and a zero exceptional model are tested.

Coefficients are exact Gaussian rationals and independent formal log(prime)
symbols in a cyclic group algebra, with order the lcm of the frequency
denominators. There is no transcendental evaluation or floating point.
The identities hold at the formal coefficient level, hence under the
usual root-of-unity evaluation. These tests complement the Lean proofs;
they are not an unbounded mathematical proof.

Separate probes check 395 non-unit prime-power support instances and
576 divisibility cases for the product of prime divisors in a cutoff.
The support/product ranges are q<=64 and n<=128.
At N=4,q=2 the omitted annular non-unit term is log(2)/4 from n=4.
At q=5 a reversed exceptional sign changes the Gauss/error identity.
The q=1 and N=0,1 cases, and odd cutoffs, are explicitly included.

The tests do not numerically certify the logarithmic/Chebyshev inequality,
a progression estimate, partial summation, an R^-5 error, or a maximal
estimate. The general finite remainder bound is a Lean proof using
Mathlib's proved Chebyshev inequality.

## Next obligations

1. Prove partial summation for the actual progression-weighted Lambda sums
   with the quadratic oscillation. The prefix-error bounds and endpoint
   terms must yield the correct normalized error, including theta*N^2.
   Mathlib.NumberTheory.AbelSummation already supplies the general Abel
   formula; inspect and reuse it before rebuilding infrastructure.
2. Verify and state the exact published prime-distribution and minor-arc
   input boundaries, with uniform constants and parameter ranges. One
   scale's exceptional data must work throughout the prefix interval
   [N/2,N], while it may change between scales.
3. Specialize M_1,M_beta to the actual source integrals, differentiate
   t^beta/beta correctly, and derive the per-residue error bounds.
4. Prove the final R^-5 major-arc bound in the permitted N,Q,R ranges and
   the annular minor-arc statement, completing Lemma 6.5.
5. Continue approximation 6.9, low 6.14, multifrequency 6.16, high/maximal
   6.21, Proposition 4.19 and the Theorem 1.1 application.

Exceptional conductor, character and beta may depend on N. Published deep
inputs may be explicit hypotheses, as authorized, but the paper's own
partial summation and deductions remain proof obligations. Lemma 3.21's
two earlier PNT limits are unchanged and unused in this unit. The frozen
manuscript and both accepted revisions are unchanged; no new source
correction is pending.

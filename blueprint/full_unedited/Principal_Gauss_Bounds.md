# Lemma 3.21: the finite Gauss-sum argument

Historical checkpoint 09 exposition. Checkpoint 10 completes the remaining
paper-specific asymptotic deduction with explicit PNT hypotheses; read
`Sharp_Gauss_Asymptotic.md` for the current complete conditional statement.

Checkpoint 09, 22 October 2026. Source: `Draft5.tex`, label `l:inftyboundsaq`,
especially `e:primepowerestimate` and `e:sproductbound`. The archived source
SHA256 remains
`d2c31b96cb15b00feac09ed4fd9a2b0482726c719c4b772320c0711875d04660`.

**The finite arithmetic part is complete. The full sharp asymptotic statement
of Lemma 3.21 is not yet complete.** All prime estimates, prime-power
vanishings, CRT coefficients, global support and the actual finite product
bound below are proved in Lean. The remaining prime-distribution/asymptotic
step is identified at the end. No new mathematical axiom or deep analytic
input has been assumed.

## Exact proved statement

For every positive integer q and every integer a coprime to q,

\[
 |\mathfrak s(a,q)|\le
 \frac4{\sqrt q}
 \prod_{\substack{p\mid q\\p>2}}(1-p^{-1/2})^{-1}.
\]

The sum vanishes if 16 divides q or an odd prime square divides q. More
explicitly, a nonzero sum implies

\[
 q=2^j d,\quad 0\le j\le3,\quad d\ge1,\quad 2\nmid d,
 \quad d\text{ squarefree}.
\]

These are unbounded results for the actual exponential sums, not numerical
observations or hypotheses about a proposed local model. The constant four
is explicit and unoptimized. Modulus one is included; modulus zero is excluded
by the positive-modulus convention.

| Component | Checked declaration |
|---|---|
| Actual complete quadratic exponential sum | `completeQuadraticGaussSum` |
| Complete prime sum times its conjugate equals p | `completeQuadraticGaussSum_mul_conj` |
| Exact prime norm sqrt(p) | `norm_completeQuadraticGaussSum_prime` |
| Unit prime sum is complete sum minus one | `unitQuadraticGaussSum_prime` |
| Unit prime sum bound sqrt(p)+1 | `norm_unitQuadraticGaussSum_prime_le` |
| Actual source normalization and sign | `principalSquareSum_as_unitGauss`, `norm_principalSquareSum` |
| Uniform normalized bound at every modulus | `norm_principalSquareSum_le_one` |
| Local odd-power and 2-power cancellation | `principalSquareSum_odd_prime_pow_eq_zero`, `principalSquareSum_two_pow_eq_zero` |
| Standard character with correct CRT scaling | `stdAddChar_crt` |
| Exact CRT for actual sums | `unitQuadraticGaussSum_coprime_mul`, `principalSquareSum_coprime_mul` |
| Actual sum bounded by proved prime-power majorants | `scaled_norm_principalSquareSum_le_product` |
| Global vanishings | `principalSquareSum_odd_prime_sq`, `principalSquareSum_sixteen_dvd` |
| Support as a squarefree odd-part decomposition | `principalSquareSum_support_decomposition` |
| Explicit finite product bound | `principalSquareSum_finite_product_bound`, its `_int` version |

## 1. Retain the actual definitions

Write

\[
 U_q(a)=\sum_{u\in A_q}e(au^2/q),\qquad
 G_q(a)=\sum_{r\bmod q}e(ar^2/q).
\]

`unitQuadraticGaussSum` was already defined in the Cohen development. The new
`completeQuadraticGaussSum` is exactly the second sum. The source's principal
normalized square sum is

\[
 \mathfrak s(a,q)=\phi(q)^{-1}U_q(-a).
\]

`principalSquareSum_as_unitGauss` checks this sign and normalization explicitly.
The norm formula divides |U_q(-a)| by the real positive totient phi(q).
All character values have norm one, so the triangle inequality and the actual
unit-group cardinality give |s(a,q)|<=1, even without a being a unit.

## 2. Evaluate the complete sum at an odd prime

Let p be odd prime and a nonzero modulo p. Multiplying the complete sum by
its complex conjugate and combining the characters gives

\[
 G_p(a)\overline{G_p(a)}
 =\sum_{u,v\bmod p}e(a(u^2-v^2)/p).
\]

The change of variables s=u-v, t=u+v is a bijection since two is invertible
modulo p. Its inverse is u=(s+t)/2, v=(t-s)/2. The formal equivalence proves
both inverse identities. Consequently the double sum is

\[
 \sum_{s,t\bmod p}e(ast/p)=p.
\]

For s=0, every term in the inner sum is one. For s nonzero, additive-character
orthogonality makes that inner sum zero. Taking the real norm square proves
|G_p(a)|=sqrt(p).

The nonunits modulo a prime consist exactly of zero, whose quadratic phase
is one. Thus U_p(a)=G_p(a)-1 and

\[
 |U_p(a)|\le\sqrt p+1,
 \qquad |\mathfrak s(a,p)|\le
 \frac{\sqrt p+1}{p-1}=\frac1{\sqrt p-1}.
\]

This proof uses a finite bijection and the already checked standard character
orthogonality. No Gauss-sum evaluation theorem is assumed as a new input.

## 3. Reuse the checked cancellation at prime powers

The earlier Cohen work constructed a permutation of the units

\[
 u\longmapsto u+t/u
\]

when t^2=0. It changes u^2 by 2t. If 2t is nonzero and a is a unit, the
quadratic sum is multiplied by a character value different from one and
therefore vanishes.

For q=p^j with p odd and j>=2, take t=p^(j-1). For q=2^j with j>=4, take
t=2^(j-2). The required square-zero and nonzero-phase conditions are proved
from exact divisibility inequalities. The new local theorems apply the
previous generic cancellation directly to U_q(a), then to s(a,q).

This establishes the local support without relying on an unproved recurrence
for the complete Gauss sum. At the three remaining powers of two the simple
bound |s|<=1 gives sqrt(2^j)*|s|<=sqrt(8)<=4.

## 4. CRT with the correct coefficients

For coprime positive m,n, define the local coefficients

\[
 a_m=(a\bmod m)n^{-1}\pmod m,\qquad
 a_n=(a\bmod n)m^{-1}\pmod n.
\]

The exact standard-character identity has these inverse-modulus factors.
Reindexing the unit sum by the checked CRT equivalence proves

\[
 U_{mn}(a)=U_m(a_m)U_n(a_n),\qquad
 \mathfrak s(a,mn)=\mathfrak s(a_m,m)\mathfrak s(a_n,n).
\]

The coefficient transforms are retained in the formal statements. This is
the CRT factorization needed in the source's multiplicativity argument.
Reduction preserves units, and each inverse-modulus factor is a unit, so
unit a produces unit a_m,a_n. The local norm bounds are uniform in these
coefficients. Multiplicativity of the totient and sqrt(mn)=sqrt(m)*sqrt(n)
give the corresponding identity for sqrt(q)*|s(a,q)|.

## 5. Assemble a proved global majorant

For a prime power p^j define a real local majorant L(p,j). Its value at j=0
is one. For j>0 it is

\[
 L(p,j)=
 \begin{cases}
 4,&p=2,\ 1\le j\le3,\\
 0,&p=2,\ j\ge4,\\
 (1-p^{-1/2})^{-1},&p>2,\ j=1,\\
 0,&p>2,\ j\ge2.
 \end{cases}
\]

Each local majorant is proved to bound the actual scaled norm at that prime
power. Define E(q) as the product of these local majorants over the canonical
prime-power factorization of q. Disjoint prime supports prove multiplicativity
of E on coprime inputs.

Induction on positive prime powers and coprime products, uniform in every
unit coefficient, then proves

\[
 \sqrt q\,|\mathfrak s(a,q)|\le E(q).
\]

Zero local factors force the global actual sum to vanish, since sqrt(q)>0.
This proves the global support criterion. Extracting the full power of two
from q and checking the remaining factorization gives the explicit odd
squarefree decomposition above, including the case d=1.

The product E has at most one factor at two, bounded by four. Every other
factor is bounded by (1-p^(-1/2))^(-1). Dividing the resulting inequality by
sqrt(q) proves the stated finite product bound for every positive q and
every unit coefficient. The integer wrapper uses the checked equivalence
between a unit integer residue modulo q and coprimality of a,q.

## 6. The remaining analytic step: precise proposed route

This subsection is a continuation specification, **not a completed Lean
proof and not an assumed input of the current project**. The full source
lemma requires the asymptotic coefficient 2+o(1) and its sufficiently-large-q
consequence with coefficient three.

Let L=log(q), let S be the prime divisors of q, and suppose L>=3. The squarefree
prime product divides q, so sum_(p in S) log(p)<=L. Put

\[
 \theta(y)=\sum_{p\le y}\log p,\qquad
 W(y)=\sum_{p\le y}p^{-1/2}.
\]

A useful finite threshold inequality is

\[
 \sum_{p\in S}p^{-1/2}
 \le W(y)+\frac{L-\theta(y)}{\sqrt y\log y},\qquad y>2.
\]

To prove it, subtract log(p)/(sqrt(y)*log(y)) from each term. The difference
is nonnegative below y and nonpositive above y, because sqrt(p)*log(p) is
increasing for p>=2. Extend the nonnegative portion to all primes below y
and use the logarithmic budget for S. This avoids needing an exact discrete
maximizer for the source's smallest-primes argument.

The standard PNT consequences theta(y)=y+o(y) and
W(y)=(2+o(1))*sqrt(y)/log(y), applied with y=L, give the leading bound needed
for the sum over S. Any use of these results must expose their exact quantified
statements and published source; the user has authorized leaving deep
published theorems unformalized. No own-paper obligation should be silently
replaced by an axiom.

The remaining correction admits an elementary bound:

\[
 \sum_{p\in S}\frac1p\le1+\log L+\frac1{\log2}.
\]

Below L, compare with the harmonic sum; above L, use the logarithmic budget
to bound the number of primes. Also

\[
 \log(1-p^{-1/2})^{-1}\le p^{-1/2}+4/p\quad(p\ge2).
\]

This follows from log(x)<=x-1 and (1-p^(-1/2))^(-1)<=4. The correction
O(log L) and the fixed log(4) are o(sqrt(L)/log(L)). Formalizing these steps,
the threshold argument, and the PNT input boundary is the next target.
Only after those are connected should the full Lemma 3.21 be marked complete.

## Verification and evidence

All 24 modules were freshly compiled with pinned Lean 4.34.1 and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`. All 227 named project theorems
pass the transitive axiom audit, allowing only propext, Classical.choice and
Quot.sound. The source scan passes for 26 Lean files. No proof placeholders,
native_decide, unsafe declarations or added mathematical axioms occur.

The independent script `check_principal_gauss.py` evaluates the actual Gauss
sums as integer polynomials modulo the cyclotomic polynomial Phi_q. These
are exact values at the primitive q-th root of unity; no floating point
arithmetic is used. For q=1,...,128 and every unit a, it checks:

- 5,022 unit coefficients in total;
- 1,688 complete odd-prime norm-square identities;
- 1,689 prime zero-term removal identities;
- 1,088 bad-modulus vanishings;
- 8,630 exact CRT comparisons, including transformed coefficients and totients;
- the modulus-one value.

These categories overlap and are not a count of distinct paper statements.
The data are in `verification/principal-gauss-numerical.json`. They are finite
supplementary checks, not inputs to Lean and not evidence for the uncompleted
sharp asymptotic. The earlier six completed paper results remain complete;
no headline theorem is yet formally verified.

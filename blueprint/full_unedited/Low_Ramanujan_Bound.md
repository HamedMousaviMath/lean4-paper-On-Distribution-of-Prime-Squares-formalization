# Lemma 3.20: a complete checked logarithmic bound

Checkpoint 08, 22 October 2026. Source: `Draft5.tex`, label `l:lowramanujan`,
near line 1885; typeset number 3.20. The archived full-source SHA256 remains
`d2c31b96cb15b00feac09ed4fd9a2b0482726c719c4b772320c0711875d04660`.

The lemma is proved as stated, for every real Q>=3 and every integer n. The
implied constant is absolute, independent of both variables. The manuscript
proof cites Mertens' theorem. The formal proof supplies an elementary sufficient
prime-product bound, so **Mertens' theorem is not an assumed input**. No change
to the statement of this lemma is needed.

## The statement and the actual sums

Keep the checked definition

\[
 C_q(n)=\sum_{u\in A_q}c_q(n-u^2),\qquad
 w_n(q)=\frac{|C_q(n)|}{q\phi(q)}.
\]

The Ramanujan sums are the genuine sums of the standard complex additive
character over units. `cohenWeight_eq` explicitly identifies the formal
`cohenWeight` with this source expression at every positive q. The harmless
natural-number extension has weight zero at q=0 and weight one at q=1.

The proved bound is

\[
 \sum_{P^+(q)<Q}w_n(q)\le C\log Q,
 \qquad C=5e^2\left(12+\frac2{\log3}\right).
\]

The constant is explicit and deliberately unoptimized. The theorem
`low_ramanujan_uniform_bound` states the uniform quantifiers as an existence
of one positive C valid simultaneously for all real Q>=3 and all integer n.

| Source/proof component | Lean declaration |
|---|---|
| Exact source absolute sum at a positive q | `cohenWeight_eq` |
| Nonnegative multiplicative weights | `cohenWeight_nonneg`, `cohenWeight_mul` |
| Finite support of the smooth series | `cohenWeight_nonzero_dvd_bound`, `smoothCohenSeries_eq_divisor_sum` |
| Euler product of the actual weights | `smoothCohenSeries_euler_product` |
| Uniform local factors | `cohenWeight_two_factor_le`, `cohenWeight_odd_prime_le` |
| Reduction to the source prime-product majorant | `smoothCohenSeries_le_prime_product` |
| Elementary weighted prime sum | `sum_log_div_prime_le` |
| Finite subset mass and logarithmic moment | `primeSubsetMass_expansion`, `primeSubsetMass_log_moment` |
| Half-mass concentration and logarithmic product bound | `primeSubsetMass_le_affine_log`, `primeSubsetMass_le_log` |
| Control of the extra local correction | `sum_inv_mul_pred_le_one`, `cohen_prime_product_le_log` |
| Full lemma for integer cutoffs | `low_ramanujan_bound_integer` |
| Full lemma for real cutoffs | `low_ramanujan_bound`, `low_ramanujan_uniform_bound` |

## 1. Establish finite support and the exact Euler product

The checked Cohen factorization gives C_q(n)=0 whenever an odd prime square
divides q or 16 divides q. This is pointwise in every integer n, so the same
vanishing holds for the nonnegative weight w_n(q).

CRT multiplicativity of C_q and multiplicativity of the totient imply
w_n(mr)=w_n(m)w_n(r) for coprime m,r. Complex norm multiplicativity handles the
absolute values. No sign restriction on C_q is assumed.

For an integer cutoff N>=3, every possible nonzero smooth coefficient divides
M=((N-1)!)^3. Conversely every divisor of M has all prime factors below N.
The formal infinite sum is therefore exactly its finite divisor sum over M.
The previously checked divisor Euler identity has been generalized from complex
values to any commutative semiring; this proof now also applies to real weights.

After the proved vanishing removes higher exponents, the exact product is

\[
 \sum_{P^+(q)<N}w_n(q)
 =(1+w_n(2)+w_n(4)+w_n(8))\prod_{2<p<N}(1+w_n(p)).
\]

This step uses proved finite support rather than an unproved interchange of
an infinite series and a product.

## 2. Bound every local factor uniformly in n

The explicit Cohen factors at 2,4,8 have absolute values at most 1,4,16.
Their denominators q*phi(q) are respectively 2,8,32. Hence

\[
 1+w_n(2)+w_n(4)+w_n(8)\le\frac52.
\]

At an odd prime p the two Cohen values are p+1 and 1-p, so

\[
 w_n(p)\le\frac{p+1}{p(p-1)}.
\]

Consequently the entire series is at most

\[
 \frac52\prod_{2<p<N}\left(1+\frac{p+1}{p(p-1)}\right).
\]

The estimates include n=0, negative n, primes dividing n, and every residue
case; no restriction on n enters the following prime-product argument.

## 3. An elementary logarithmically weighted prime sum

Let S be any finite set of primes p<=N. The first term of Legendre's formula
for the factorial gives floor(N/p)<=v_p(N!). Multiplication by log(p)>=0 and
summation therefore give

\[
 \sum_{p\in S}\left\lfloor\frac Np\right\rfloor\log p\le\log(N!).
\]

The elementary bound N!<=N^N implies log(N!)<=N log(N). Also

\[
 \sum_{p\in S}\log p
 \le\log\!\left(\prod_{p\le N}p\right)\le N\log4,
\]

using the primorial bound already proved in pinned Mathlib. Since
N/p<=floor(N/p)+1, the two estimates imply

\[
 \sum_{p\in S}\frac{\log p}{p}\le\log N+\log4.
\]

The actual factorial, prime factorization and primorial inequalities are used
in Lean. This is not an assumed weighted-prime estimate.

## 4. The subset expansion and its first logarithmic moment

For t a subset of S put d(t)=product_(p in t) p, including d(empty)=1. Define

\[
 P(S)=\prod_{p\in S}\left(1+\frac1p\right)
 =\sum_{t\subseteq S}\frac1{d(t)}.
\]

Distinct subsets have distinct products, by unique prime factorization.
Expanding the finite product and its first logarithmic moment gives

\[
 \sum_{t\subseteq S}\frac{\log d(t)}{d(t)}
 =P(S)\sum_{p\in S}\frac{\log p}{p+1}.
\]

`weighted_powerset_moment` proves the underlying product identity by induction
on S. It imposes no probability-theoretic assumption. The logarithm of the
product is then identified with the sum of the logarithms.

For N>=3, log4<=2 log(N). The preceding weighted-prime sum therefore yields

\[
 \sum_{t\subseteq S}\frac{\log d(t)}{d(t)}\le3P(S)\log N.
\]

## 5. Concentrate the mass below N^6

Let A be the reciprocal mass of subsets with d(t)<=N^6, and B the remaining
mass. Then P=A+B. Every product in B has log d(t)>=6 log N, so the moment
bound gives

\[
 6B\log N\le3P\log N,\qquad B\le P/2.
\]

The products counted in A are distinct positive integers at most N^6. Thus
A<=H_(N^6), where H is the harmonic sum. The checked bound
H_m<=1+log(m) gives

\[
 P\le2A\le2+12\log N
 \le\left(12+\frac2{\log3}\right)\log N.
\]

This proves the sufficient Mertens-type upper bound by finite sums and an
elementary harmonic estimate. It does not assert Mertens' asymptotic formula.

## 6. Control the summable correction in the source product

For p>=2,

\[
 1+\frac{p+1}{p(p-1)}
 =1+\frac1p+\frac2{p(p-1)}
 \le\left(1+\frac1p\right)\left(1+\frac2{p(p-1)}\right).
\]

The elementary telescoping identity

\[
 \sum_{j=0}^{m-1}\frac1{(j+1)(j+2)}=1-\frac1{m+1}
\]

implies sum_(p in S) 1/(p(p-1))<=1. Applying 1+u<=exp(u) to the
nonnegative correction factors shows their product is at most e^2. Hence

\[
 \prod_{p\in S}\left(1+\frac{p+1}{p(p-1)}\right)
 \le e^2\left(12+\frac2{\log3}\right)\log N.
\]

Combining with the factor 5/2 proves the integer-cutoff estimate with constant
C/2. Every sum and product in this argument is finite.

## 7. Preserve the strict cutoff for all real Q>=3

Put N=ceil(Q). For an integer prime p, p<N is equivalent to p<Q, including
exact prime endpoints. Thus the real-cutoff series is exactly the already
bounded integer-cutoff series. Since Q>=3, N<=Q^2 and log N<=2 log Q.
The additional factor two gives the stated constant C for all real Q>=3.

## Verification and scope

All 21 modules were freshly compiled locally with pinned Lean 4.34.1 and
Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`. All 186 named project
theorems pass the transitive axiom audit: only propext, Classical.choice and
Quot.sound occur. The source scan passes for 23 Lean files. There are no
proof placeholders, native proof shortcuts, or added mathematical axioms.

The exact rational experiment checks 4,640 cases, covering every residue
class in the full period for each of twelve integer/noninteger cutoffs. The
actual supported-modulus sum agrees with its Euler product and satisfies the
rational local-factor majorant in every case. See
`verification/low-ramanujan-numerical.json`. The logarithmic estimate is proved
in Lean; these finite experiments supply supplementary evidence.

The user has confirmed applying both the Lemma 3.14 and Corollary 3.16 statement
replacements. No further correction is requested for those supplied updates.
The archived full source and PDF retain their original hashes. No headline
theorem is yet complete and no deep analytic input has been assumed.

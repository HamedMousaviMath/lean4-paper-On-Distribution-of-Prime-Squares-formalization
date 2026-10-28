# Corrected progression Euler product: checked proof specification

**Checkpoint 07 update:** the user has supplied the corrected Lemma 3.14.
It matches this checked statement; the earlier statement issues are resolved
for that revision. The full archived source remains unchanged. See
`docs/SOURCE_UPDATE_07.md`. The proof below is the completed checkpoint 06 proof.

Checkpoint 06, 22 October 2026. Source: the locked `sources/current/Draft5.tex`,
Lemma 3.14, label `l:motamakemajorprimesquareprog`, equation `e:corupss`.
Its SHA256 remains
`d2c31b96cb15b00feac09ed4fd9a2b0482726c719c4b772320c0711875d04660`.

The complete Euler-product identity is proved with **Q>2 and positive k**.
The last vanishing assertion is proved with the necessary restriction **p<Q**
on the obstructing prime. The original statement needs these qualifications;
it is not counted as proved verbatim. Both missing qualifications have
kernel-checked counterexamples. See `docs/SOURCE_FINDINGS_06.md` and the
replacement statement in `corrections/Lemma_3_14_Replacement.tex`.

## Statement being proved

For q,k positive and b,x arbitrary integers, use exactly the previously
formalized exponential sums from Lemma 3.12 and put

\[
 B(q;k,b,x)=\sum_{a\in A_q}\Upsilon(a,q,b,k)\mathfrak s(a,q)e(ax/q).
\]

For Q>2, k>=1 and gcd(b,k)=1, the smooth-modulus sum equals

\[
 \sum_{P^+(q)<Q}B(q;k,b,x)
 =\mathcal T_2\prod_{2<p<Q}E_p(k,b,x),
\]

where h=v_2(k),

\[
 \mathcal T_2=
 \begin{cases}
 1+(-1)^x,&h=0,\\
 2^{\min(h,3)}\mathbf1_{x-b\equiv1\pmod{2^{\min(h,3)}}},&h>0,
 \end{cases}
\]

and the four cases of the odd-prime factor are

\[
 E_p=
 \begin{cases}
 1+(p+1)/(p-1),&p\mid k,\ (\frac{x-b}{p})=1,\\
 0,&p\mid k,\ (\frac{x-b}{p})\ne1,\\
 1-(p+1)/(p-1)^2,&p\nmid k,\ (\frac{x}{p})=1,\\
 1+1/(p-1),&p\nmid k,\ (\frac{x}{p})\ne1.
 \end{cases}
\]

A single product of this case-defined factor is the same mathematical formula
as the four products in the source: the four conditions partition the odd
primes below Q. No condition has been omitted at Legendre-symbol value zero.
The formal local definition uses a harmless unused branch for nonprime p.

The vanishing consequence is: if an odd prime **p<Q** divides k and
( (x-b)/p ) is not 1, the smooth-modulus sum is zero.

| Source component | Checked declaration |
|---|---|
| Actual coefficient B, not an assumed local formula | `progressionCoefficient`, `progressionCoefficient_eq` |
| Its exact normalization and C_q representation | `progressionCoefficient_as_quadratic` |
| Multiplicativity in q | `progressionCoefficient_mul` |
| Uniform support at all moduli | `progressionCoefficient_odd_prime_sq`, `progressionCoefficient_sixteen_dvd` |
| Genuine reduction of the series to a finite sum | `smoothProgressionSeries_eq_divisor_sum` |
| Euler product of actual local coefficients | `smoothProgressionSeries_euler_product` |
| Four explicit odd-prime factors | `progressionCoefficient_odd_euler_factor` |
| Complete T_2 factor | `progressionCoefficient_two_euler_factor` |
| Corrected identity, integer cutoff Q>=3 | `progression_euler_product` |
| Corrected identity, every real cutoff Q>2 | `progression_euler_product_real` |
| Corrected obstruction consequence | `progression_euler_product_eq_zero_of_obstruction` |
| Counterexamples to the omitted restrictions | `cutoff_two_counterexample`, `obstructing_prime_above_cutoff_counterexample` |

All names are in namespace `PrimeSquares`. The files added are
`EulerCoefficient.lean`, `SmoothEuler.lean` and `LocalEuler.lean`.

## 1. Open the sums in the useful order

Write g=gcd(q,k), and retain the genuine quadratic Cohen correlation
C_q(n)=sum_(u in A_q) c_q(n-u^2), completed in Lemma 3.1.
Opening the two exponential sums, then summing over a and next over u,
gives the exact identity

\[
 B(q;k,b,x)=\frac{\phi(k)}{\phi(q)\phi([k,q])}
 \sum_{\substack{r\in A_q\\r\equiv b\pmod g}}C_q(x-r).
\]

The existing normalized expansion from Lemma 3.12 proves this finite
reordering. The new proof explicitly checks x-u^2-r=x-r-u^2.
For every multiplicative arithmetic function f,
f(lcm(q,k)) f(gcd(q,k))=f(q)f(k). Applying Mathlib's proved identity to
f=phi gives phi(lcm(q,k)) phi(g)=phi(q) phi(k), hence

\[
 B(q;k,b,x)=\frac{\phi(g)}{\phi(q)^2}
 \sum_{\substack{r\in A_q\\r\equiv b\pmod g}}C_q(x-r). \tag{1}
\]

All cancelled totients are first proved nonzero. The coefficient is extended
by zero at q=0 solely to use natural-number arithmetic-function interfaces;
agreement with the actual exponential sum at every positive q is proved.

Formula (1) needs neither coprimality of b and k nor a distribution theorem.
This stronger formulation simplifies the support and multiplicativity proofs.

## 2. Multiplicativity includes the restriction and weight

Let gcd(m,n)=1. Then

\[
 \gcd(mn,k)=\gcd(m,k)\gcd(n,k),
 \qquad \gcd(\gcd(m,k),\gcd(n,k))=1.
\]

The ring CRT and its checked unit equivalence identify A_(mn) with A_m×A_n.
The progression restriction modulo gcd(mn,k) is exactly the conjunction of
the two coordinate restrictions. This equivalence is proved through the
canonical reduction homomorphisms, rather than postulated.

The already checked identity C_(mn)(z)=C_m(z)C_n(z), with explicit reductions,
separates the summand. The two finite unit sums consequently factor. Totient
multiplicativity separates phi(gcd(mn,k))/phi(mn)^2 into the corresponding
weights at m and n. Thus

\[
 B(mn;k,b,x)=B(m;k,b,x)B(n;k,b,x).
\]

At modulus one the unit group has one element, its character is one and
B(1;k,b,x)=1. The proofs include this case and the zero extension.

## 3. Uniform vanishing gives finite support

For an odd prime p, if p^2 divides q then C_q(n)=0 for every n. If 16 divides
q then C_q(n)=0 for every n. These follow from the completed global
prime-power factorization of C: one local factor in its product vanishes.
The divisibility-to-valuation bridge is formally checked.

Formula (1) therefore proves, for arbitrary b and x,

\[
 p^2\mid q,\ p>2\ \Longrightarrow\ B(q;k,b,x)=0,
 \qquad 16\mid q\ \Longrightarrow\ B(q;k,b,x)=0.
\]

This is a statement about all moduli, not just isolated prime powers.
Only squarefree odd parts and a power of two of exponent at most three
can contribute.

For an integer cutoff Q>=3, choose the convenient bound

\[
 N_Q=((Q-1)!)^3.
\]

It is not intended as an optimal bound. If every prime divisor of q is
below Q and B(q;k,b,x) is nonzero, then q divides N_Q. Indeed, every prime
of q divides (Q-1)!, so its exponent in N_Q is at least three, while its
exponent in a nonzero coefficient is at most three. Comparing all prime
valuations proves the divisibility.

Conversely, every divisor of N_Q has all prime factors below Q. Consequently

\[
 \sum_{P^+(q)<Q}B(q;k,b,x)=\sum_{q\mid N_Q}B(q;k,b,x). \tag{2}
\]

The formal proof uses `tsum_eq_sum`, with a proof that every summand outside
the divisor set is zero. Thus the complex-valued series has finite support;
no conditional rearrangement, unproved convergence or analytic input occurs.
Smoothness is modeled by the equivalent prime-divisor condition. For q=1,
this agrees with the source convention P^+(1)=1 because Q>2. The extension
at q=0 contributes zero.

## 4. The finite divisor Euler product

For a multiplicative function f with f(0)=0 and f(1)=1, the divisor sum is
the Dirichlet convolution (f*zeta)(N). Mathlib proves multiplicativity of
this convolution. Applying the natural-number prime-power factorization to
it, then identifying the divisors of p^a with p^j, 0<=j<=a, yields

\[
 \sum_{d\mid N}f(d)
 =\prod_{p\mid N}\left(\sum_{j=0}^{v_p(N)}f(p^j)\right).
\]

This argument is formalized in `sum_divisors_multiplicative` and is applied
to the actual B. The primes of N_Q are exactly the primes below Q, each with
valuation at least three. The previously proved vanishings truncate the
odd-prime exponent sums after one, and the exponent sum at two after three.
Equation (2) becomes

\[
 \bigl(1+B(2)+B(4)+B(8)\bigr)
 \prod_{2<p<Q}\bigl(1+B(p)\bigr). \tag{3}
\]

This proves the Euler-product step before any explicit local evaluation.

## 5. Local evaluations

If q divides k and b is a unit modulo q, the restriction in (1) fixes r=b.
Thus B(q)=C_q(x-b)/phi(q). If gcd(q,k)=1 the restriction disappears; opening
C and applying the ordinary linear Cohen identity gives

\[
 \sum_{r\in A_q}C_q(x-r)=\mu(q)C_q(x),
 \qquad B(q)=\mu(q)C_q(x)/\phi(q)^2.
\]

For p^a with a>=2 which does not divide k, write gcd(p^a,k)=p^j. If j=0,
mu(p^a)=0. If 0<j<a, the gcd and complementary modulus share p, so the
completed progression Cohen identity kills the coefficient. This also proves
the partial-overlap cases for powers of two. Coprimality of b and k supplies
every unit-class hypothesis via divisibility.

For odd primes, insert the completed evaluation C_p(n)=p+1 for Legendre
symbol 1, and 1-p otherwise, and use mu(p)=-1 and phi(p)=p-1. Adding 1 to
the coefficient gives precisely the four factors E_p displayed above.
Nonzero denominators are proved from primality.

## 6. The 2-adic sum

If v_2(k)=0, only B(2) can contribute and B(2)=(-1)^x. Otherwise the allowed
terms are C_(2^a)(x-b)/phi(2^a), for 1<=a<=min(v_2(k),3).
The complete signed factors from Lemma 3.1 give

\[
 \begin{aligned}
 1+C_2(n)&=2\mathbf1_{n\equiv1\pmod2},\\
 1+C_2(n)+C_4(n)/2&=4\mathbf1_{n\equiv1\pmod4},\\
 1+C_2(n)+C_4(n)/2+C_8(n)/4&=8\mathbf1_{n\equiv1\pmod8}.
 \end{aligned}
\]

The small congruence predicates are checked by Lean's kernel using `decide`;
the complex arithmetic and the relation of the residues at 2,4,8 are proved
explicitly. This is not `native_decide` or an external numeric oracle.
Splitting the valuation of k into 0,1,2,>=3 proves exactly T_2 in the source,
including arbitrary negative integer x and b.

## 7. Real cutoffs and the corrections

For every real Q>2 and integer prime p, p<ceil(Q) if and only if p<Q.
Moreover ceil(Q)>=3. Mathlib's proved `Nat.lt_ceil` transports the integer
cutoff theorem to every real cutoff Q>2 without changing the included primes.

At Q=2 the literal smooth series is 1. With k=1, b=x=0 the displayed 2-adic
factor is 2, so the unqualified identity fails. For the vanishing sentence,
Q=3, k=5, b=1, x=4 gives a series equal to 2, while x-b=3 is a nonsquare
modulo five. Both assertions are proved in Lean. The corrected obstruction
theorem explicitly requires p<Q; the prime then supplies an actual zero
factor in (3).

The replacement LaTeX fragment changes only the statement's cutoff, modulus
range and final obstruction restriction. It preserves the displayed identity,
T_2 formula and labels. The locked authoritative source is unchanged.

## Verification and remaining work

All fifteen project modules build. The source scan covers seventeen Lean files
and rejects proof placeholders, extra axioms, native_decide and unsafe code.
All 120 named project theorems pass the transitive axiom audit, allowing only
`propext`, `Classical.choice` and `Quot.sound`.

The independent exact-integer/rational experiment passes 94,208 fixed-modulus
cases with 1<=q<=128, 1<=k<=12, all unit b modulo k and 0<=x<=15. It also
passes 3,680 finite Euler-product comparisons for integer cutoffs 3 through 7.
These experiments use the classical Ramanujan divisor formula; they do not
supply the universal support proof or the formal counterexamples.

Three earlier numbered paper lemmas are complete as stated within positive
modulus conventions; this checkpoint adds the corrected version of Lemma 3.14.
No headline theorem or general-coefficient Corollary 3.16 is complete. No deep
analytic theorem has been assumed. The next target is Corollary 3.16; the new
multiplicativity, support and finite Euler-product infrastructure should be
reused, with the progression coefficient multiplied by its general integer ell.

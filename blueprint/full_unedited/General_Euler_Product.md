# Corollary 3.16: checked proof and source correspondence

**Checkpoint 08 update:** the user has confirmed applying the supplied
statement replacement. Its explicit ranges are accepted; no further edit to
that supplied statement is requested. The proof below was completed in
checkpoint 07. See `docs/SOURCE_UPDATE_08.md`.

Checkpoint 07, 22 October 2026. Source label:
`c:generalmajorprimesquareprog`; equations `e:generalcorupss`,
`e:generalT2` and `e:fixedqcoefficient`. The archived source is
`sources/current/Draft5.tex`, SHA256
`d2c31b96cb15b00feac09ed4fd9a2b0482726c719c4b772320c0711875d04660`.

The identity is proved for every real Q>2, every positive integer k, and all
integers ell,b,n satisfying gcd(b,k)=1. There is **no coprimality or nonzero
condition on ell**. The actual exponential sums, local counts, normalization,
finite support and complete Euler product are connected in Lean.

The corollary should state the same cutoff and modulus conventions now explicit
in the user's revised Lemma 3.14. A statement fragment with this opening is in
`corrections/Corollary_3_16_Replacement.tex`. Its displayed formulas are unchanged.
See `docs/SOURCE_UPDATE_07.md` for the accepted Lemma 3.14 revision and the
distinction between the supplied update and the archived full draft.

## Definitions and target

For a positive modulus q let A_q be its unit residue classes and set

\[
 B_\ell(q;k,b,n)=\sum_{a\in A_q}
 \Upsilon(a\ell,q,b,k)\mathfrak s(a,q)e(an/q).
\]

The definition `generalCoefficient` uses exactly the existing `upsilon`,
`principalSquareSum` and standard complex additive character. It is extended
by zero at q=0, solely to use natural-number arithmetic functions. The paper
sums over positive q. The extension contributes zero to the formal series.

For each odd prime p define the genuine finite cardinality

\[
 N_p=\#\{(u,v)\in A_p^2:
 u^2+\ell v\equiv n\pmod p,\quad v\equiv b\pmod{(p,k)}\}.
\]

The formal definition `primeSolutionCount` is the cardinality of this filtered
product of unit groups. Congruence modulo gcd(p,k) is implemented by the
canonical reduction homomorphism. Equality in ZMod p implements the first
congruence. Its irrelevant value at p=0 is defined as zero.

The target is

\[
 \sum_{P^+(q)<Q} B_\ell(q;k,b,n)
 =\mathcal T_2(\ell,k,n;b)
 \prod_{2<p<Q}\frac{p\phi((p,k))}{(p-1)^2}N_p,
\]

with exactly the finite 2-adic factor given in the source. Products over an
empty prime set have value one. At q=1, the coefficient is one; this endpoint
is proved directly, without a prime-factor calculation at a zero modulus.

## 1. Expand the actual coefficient

Put g=gcd(q,k) and write psi_q for the standard additive character.
Opening Upsilon(a*ell) contributes psi_q(-a*ell*v), the square sum contributes
psi_q(-a*u^2), and the remaining phase contributes psi_q(a*n).
Their product is psi_q(a*(n-u^2-ell*v)). Summing over unit a gives the
Ramanujan sum c_q(n-u^2-ell*v). All sums in this step are finite, so their
order may be interchanged.

Thus, with

\[
 R_\ell(q)=\sum_{\substack{u,v\in A_q\\v\equiv b\pmod g}}
 c_q(n-u^2-\ell v),
\]

the exact source normalization is

\[
 B_\ell(q)=\frac{\phi(k)}{\phi(q)\phi([k,q])}R_\ell(q).
\]

`general_correlation_expansion` checks the phases and signs.
`generalCoefficient_fixed_modulus` proves equation `e:fixedqcoefficient`.
The scalar identity phi(lcm(q,k))*phi(gcd(q,k))=phi(q)*phi(k), with positive
totients when cancelled, gives the equivalent normalization

\[
 B_\ell(q)=\frac{\phi(g)}{\phi(q)^2}
 \sum_{\substack{v\in A_q\\v\equiv b\pmod g}} C_q(n-\ell v),
 \qquad C_q(t)=\sum_{u\in A_q}c_q(t-u^2).
\]

This is `generalCoefficient_as_quadratic`. It also proves that ell=0 causes
no difficulty: no inverse of ell and no substitution dividing by ell is used.

## 2. Multiplicativity

For coprime m and r, the unit CRT identifies A_(mr) with A_m times A_r.
The previously proved identity for C_(mr) separates its two coordinates.
Reduction maps preserve subtraction, multiplication and integer casts, so
n-ell*v becomes the corresponding n-ell*v in each coordinate.

The progression restrictions separate because
gcd(m*r,k)=gcd(m,k)*gcd(r,k), and those two gcds are coprime. The totient
normalization separates by totient multiplicativity. Consequently

\[
 B_\ell(mr)=B_\ell(m)B_\ell(r),\qquad B_\ell(1)=1.
\]

These statements concern the actual coefficient, established by
`scaled_quadratic_filtered_crt`, `generalCoefficient_mul` and
`generalCoefficient_one`. Neither b being a unit nor any restriction on ell
is needed for this part when k is positive.

## 3. Prove finite support before forming an Euler product

The completed quadratic Cohen identity implies pointwise C_q(t)=0 for every
integer t if an odd prime square divides q or if 16 divides q. Substitution
t=n-ell*v transfers this vanishing to B_ell(q), uniformly in every parameter.
Thus a nonzero coefficient can only have odd-prime exponents zero or one
and exponent at two at most three.

For an integer cutoff Q>=3, put M=((Q-1)!)^3. Every nonzero smooth coefficient
has q dividing M. Every divisor of M has all its prime divisors below Q.
The formal infinite sum therefore equals the finite divisor sum

\[
 \sum_{P^+(q)<Q}B_\ell(q)=\sum_{q\mid M}B_\ell(q).
\]

This is `smoothGeneralSeries_eq_divisor_sum`. The finite divisor Euler
identity `sum_divisors_multiplicative`, already proved in checkpoint 06, then
applies. The vanishing rules shorten the exponent sums and yield

\[
 \sum_{P^+(q)<Q}B_\ell(q)
 =(1+B_\ell(2)+B_\ell(4)+B_\ell(8))
 \prod_{2<p<Q}(1+B_\ell(p)).
\]

This is `smoothGeneralSeries_euler_product`. No analytic convergence theorem
or rearrangement assumption is used.

## 4. Evaluate each prime factor by an actual pair count

At a prime p, the exponential definition of the Ramanujan sum has already
been proved to give c_p(t)=p*1_(t=0)-1. Let M_p be the number of unit pairs
satisfying only the progression restriction on v. Opening this formula gives

\[
 R_\ell(p)=pN_p-M_p.
\]

To count M_p there are two cases. If p does not divide k, the gcd is one,
so every v is allowed and M_p=(p-1)^2. If p divides k, coprimality of b and k
ensures b is a unit modulo p; the condition fixes exactly v=b and leaves
p-1 choices for u. In both cases

\[
 \phi((p,k))M_p=(p-1)^2.
\]

The proofs `prime_progression_unit_mass` and `prime_progression_pair_mass`
establish this count and use the actual unit-group cardinality phi(p).
With w_p=phi((p,k))/(p-1)^2, one obtains

\[
 1+B_\ell(p)=1+w_p(pN_p-M_p)=p w_pN_p.
\]

This is `generalCoefficient_prime_euler_factor`. In particular, zero solution
counts, primes dividing ell, ell=0, and n=0 need no separate exclusions.

## 5. Keep the exact source factor at two

For nu=1,2,3 use the proved fixed-q identity at q=2^nu. The sum
1+B_ell(2)+B_ell(4)+B_ell(8) is exactly

\[
 1+\sum_{\nu=1}^3
 \frac{\phi(k)}{\phi(2^\nu)\phi([k,2^\nu])}
 \sum_{\substack{u,v\in A_{2^\nu}\\v\equiv b\pmod{(2^\nu,k)}}}
 c_{2^\nu}(n-u^2-\ell v).
\]

This is the definition `generalTwoEulerFactor`, with the source's exponent
range represented by j=0,1,2 and nu=j+1. Its identification with the local
coefficient sum is `generalCoefficient_two_euler_factor`. Higher powers have
already been proved to vanish. No further assumption on a 2-adic factor is made.

## 6. Assemble the identity and handle real cutoffs

`general_progression_euler_product` combines the finite product and the local
evaluations for integer Q>=3. For any real Q>2, an integer prime satisfies
p<Q exactly when p<ceil(Q). Using this equivalence proves
`general_progression_euler_product_real`, with precisely the strict prime
cutoff in the paper. This includes nonintegral Q and exact prime endpoints.

Two consistency results connect the new definitions to the earlier lemma:
`generalCoefficient_one_multiplier` identifies B_1 with the old coefficient
at every natural q, and `generalTwoEulerFactor_one_multiplier` identifies
its 2-adic factor with the previous closed valuation formula.

## Verification and limits

All 18 project modules build with pinned Lean 4.34.1 and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`. The 150 named project theorems,
including 30 new declarations, pass the transitive axiom audit: only propext,
Classical.choice and Quot.sound occur. There are no proof placeholders or
additional mathematical axioms. The source audit scans 20 Lean files.

The separate script `check_general_euler_product.py` passes 109,824 exact
fixed-modulus comparisons and 13,728 finite Euler comparisons. The ranges,
signed representatives and zero/negative multipliers are recorded in
`verification/general-euler-numerical.json`. All arithmetic uses integers
and rational Fractions. These are finite experiments, not inputs to Lean.

This finishes the corollary with the stated ranges. It does not complete a
headline theorem of the paper or the general character-twisted square sum.
No deep analytic result has yet been assumed.

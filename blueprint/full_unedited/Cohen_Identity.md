# Quadratic Cohen identity: completed formalization

Source: `sources/current/Draft5.tex`, Lemma 3.1, label `l:cohenquadratic`,
on page 17 of the supplied 99-page PDF. The complete identity and its uniform
bound are proved in Lean. This is the first complete numbered paper lemma in
the project; the other paper results remain open.

## Statement and definitions

For a positive integer q, write A_q for the units of Z/qZ and define

\[
 c_q(m)=\sum_{a\in A_q}\exp(2\pi i am/q),\qquad
 C_q(n)=\sum_{r\in A_q}c_q(n-r^2).
\]

Let \(a=v_2(q)\) and \(d=q/2^a\). The checked global statement is

\[
 C_q(n)=|\mu(d)|T_a(n)
 \prod_{\substack{p\mid q\\p>2}}
 \begin{cases}
  p+1,&\left(\frac np\right)=1,\\
  1-p,&\left(\frac np\right)\ne1.
 \end{cases}
\]

It holds for every positive q and every integer n, including negative n.
The modulus-one product is empty and has value 1. The Legendre symbol has
value zero when p divides n, and that case is included in the second branch.

The 2-adic factor is represented explicitly in the code:

| Exponent a | Nonzero values of T_a(n) | All other residues |
|---|---|---|
| 0 | 1 for every n | — |
| 1 | +1 at n=1 modulo 2; -1 at n=0 modulo 2 | — |
| 2 | +4 at n=1 modulo 4; -4 at n=3 modulo 4 | 0 |
| 3 | +16 at n=1 modulo 8; -16 at n=5 modulo 8 | 0 |
| a>=4 | None | 0 |

This is the paper's T_a, with the signs spelled out. The equivalence is also
checked: `twoAdicCohenFactor_one` proves \(T_1(n)=(-1)^{n+1}\), using integer
powers, and `twoAdicCohenFactor_small` proves
\(T_a(n)=\phi(2^a)c_{2^a}(n-1)\) for a=2,3. The explicit residue cases give
the zero and signed-square assertions in the paper.

The formalization also proves

\[
 |C_q(n)|\leq16\,|\mu(q/2^a)|\prod_{p\mid q}(p+1).
\]

The absolute constant 16 suffices for the paper's implied-constant bound.
The sharper constant 16/3 is not asserted as a universal Lean theorem here.

## 1. Genuine exponential sums

`PrimeSquares/QuadraticCohen.lean` uses Mathlib's `ZMod.stdAddChar`, whose value
on an integer residue is the displayed complex exponential. It defines c_q
and C_q by finite sums over a complete residue system filtered by `IsUnit`.
`sum_unit_filter_eq_sum_units` proves the equivalence with summing directly
over the unit group. Modulus zero is excluded from these definitions by
`NeZero q`.

The assembly file introduces `cohenCorrelation q n` as an integer-input
interface. `cohenCorrelation_eq` proves that it is exactly C_q(n) whenever
q>0. Its arbitrary zero extension at q=0 is used only to apply the standard
multiplicative-function factorization theorem; q=0 is excluded from the main
identity and bound.

## 2. Odd prime factor

Additive-character orthogonality gives

\[
 \sum_{a\bmod p}e(am/p)=
 \begin{cases}p,&m=0\pmod p,\\0,&m\ne0\pmod p.\end{cases}
\]

For prime p, units are precisely nonzero residues, so subtracting the zero
term proves \(c_p(m)=p-1\) when m=0 and -1 otherwise.

Let R be the number of all roots of \(r^2=n\) modulo p. Summing over all r
and subtracting the r=0 summand gives

\[
 C_p(n)=pR-p-c_p(n).
\]

Mathlib's `legendreSym.card_sqrts` proves \(R=(n/p)+1\) for odd p. If p
 divides n, R=1 and the formula gives 1-p. Otherwise the Legendre symbol is
+1 or -1, giving p+1 or 1-p. This proves `quadraticRamanujanSum_odd_prime`
with no assumption that n is a unit.

## 3. Higher prime powers by a unit permutation

The code uses one algebraic argument for both higher-power vanishings, in
place of the paper's separate Hensel-lifting count and 2-adic permutation.

Let R be a commutative ring, \(t^2=0\), and r a unit. Then

\[
 F_t(r)=r+t/r
\]

is a unit: its multiplicative inverse is \(r^{-1}-tr^{-3}\). Moreover
\(F_{-t}\) is the inverse permutation to \(F_t\), and

\[
 F_t(r)^2=r^2+2t.
\]

All three assertions are proved in `UnitSquareShift.lean`, including
bijectivity and the explicit inverse. Define the unit quadratic Gauss sum

\[
 S_q(b)=\sum_{r\in A_q}e(br^2/q).
\]

For unit b, reindexing by F_t gives

\[
 S_q(b)=e(2bt/q)S_q(b).
\]

When \(2t\ne0\) modulo q, primitivity of the standard character and
invertibility of b make the multiplier different from 1. Thus S_q(b)=0.
Expanding c_q and interchanging the finite sums then gives

\[
 C_q(n)=\sum_{b\in A_q}e(bn/q)S_q(-b)=0.
\]

For \(q=p^k\), p odd and k>=2, take \(t=p^{k-1}\). The divisibility
\(q\mid t^2\) follows from 2k-2>=k, while 2t is nonzero since p does not
divide 2. For \(q=2^a\), a>=4, take \(t=2^{a-2}\). Again t squared is
zero modulo q, and \(2t=2^{a-1}\ne0\). The inequalities, divisibility,
and nonvanishing are proved for all exponents, not checked up to a bound.

## 4. Small powers of two

For q=2,4,8 every unit square is 1. Kernel-reduced `decide` checks these
finite unit assertions and their counts, giving

\[
 C_2(n)=c_2(n-1),\quad C_4(n)=2c_4(n-1),\quad C_8(n)=4c_8(n-1).
\]

To evaluate c_4 and c_8, subtract the even residues from the complete
additive-character sum. `stdAddChar_scale` identifies the even-residue sum
with the complete character sum at half the modulus. Orthogonality gives

\[
 c_4(m)=\begin{cases}2,&m=0\pmod4,\\-2,&m=2\pmod4,\\0,&\text{otherwise},\end{cases}
\]

and c_8 has values +4 at 0, -4 at 4 modulo 8, and zero elsewhere. These
are symbolic proofs of the complex-valued sums. Finite unit sets and
projection kernels are the only computational residue checks. The modulus-one
case uses the trivial ring's unit and character conventions and gives C_1=1.

## 5. CRT multiplicativity with the normalization proved

For coprime positive u,v, CRT identifies the units modulo uv with the
product of the two unit groups. For the coefficients inside c_q use

\[
 (b,c)\longmapsto vb+uc\pmod{uv}.
\]

Its CRT coordinates are (vb,uc). Multiplication by v modulo u and by u
modulo v are unit permutations, so this is a bijection of the coefficient
sets. The character-scaling identities

\[
 e(vj/(uv))=e(j/u),\qquad e(uj/(uv))=e(j/v)
\]

are proved from the actual exponential formula. Reindexing the coefficient
sum therefore proves c_(uv)(m)=c_u(m)c_v(m). Reindexing the square-shift
variable by ordinary CRT then proves

\[
 C_{uv}(n)=C_u(n)C_v(n).
\]

This avoids assuming an incorrect unscaled factorization of the standard
character itself. Both multiplicativity theorems include u=1 or v=1.

## 6. Prime-factor and Mobius assembly

`cohenCorrelation_factorization` applies multiplicativity to the canonical
prime-power factorization. At an odd prime, the local contribution is its
Legendre factor if the exponent is one, and zero for every higher exponent.
Consequently the product of exponent-one indicators is 1 exactly when the
odd modulus is squarefree. `primeFactor_indicator_eq_abs_moebius` identifies
this product with \(|\mu(d)|\).

Mathlib's prime-power projection gives

\[
 q=2^a d,\qquad d>0,\qquad 2\nmid d,
\]

and the prime factors of d are exactly the prime factors of q greater than 2.
Combining the odd product with the complete T_a factor proves the global
identity. This includes q=1 and all nonsquarefree odd parts.

## 7. Uniform bound

The explicit local cases prove \(|T_a(n)|\leq16\) for every a,n. Each odd
Legendre factor has absolute value at most p+1. The Mobius absolute value
is nonnegative, so taking norms of the product gives the displayed bound
with constant 16, after enlarging the odd-prime product to all prime factors.
This is `quadratic_cohen_bound`.

## Checked declarations and source correspondence

| Paper component | Main Lean declaration |
|---|---|
| Definition of c_q and C_q | `ramanujanSum`, `quadraticRamanujanSum` |
| Positive-modulus integer interface | `cohenCorrelation_eq` |
| Odd-prime formula, e:Cp | `quadraticRamanujanSum_odd_prime` |
| Odd higher powers vanish | `quadraticRamanujanSum_odd_prime_pow` |
| Higher powers of two vanish | `quadraticRamanujanSum_two_pow_ge_four` |
| Complete factors at 4 and 8 | `quadraticRamanujanSum_four_explicit`, `quadraticRamanujanSum_eight_explicit` |
| Parity and totient expressions, e:Ta | `twoAdicCohenFactor_one`, `twoAdicCohenFactor_small` |
| Multiplicativity, e:Cmultiplicative | `quadraticRamanujanSum_coprime_mul` |
| Global product, e:cohenquadratic | `quadratic_cohen_identity` |
| Uniform bound, e:CohenQuadratic | `quadratic_cohen_bound` |

## Verification and scope

The root project imports all nine modules. The complete build and transitive
axiom audit cover all 57 named project theorem declarations, including the
initial support lemmas. Only `propext`, `Classical.choice`, and `Quot.sound`
occur. No deep analytic input, extra mathematical axiom, proof placeholder,
or `native_decide` is used in this development.

The exact Python experiment over every n modulo every 1<=q<=512 passed
131,328 cases. It uses the classical Ramanujan divisor formula and is separate
from the universal Lean proof. Its sharper finite bound check with constant
16/3 is not needed for the formal bound with constant 16.

Lemma 3.1 is complete. The next finite-arithmetic targets are the ordinary
Cohen identity, `l:progressioncohen`, and `l:sumoverramanujan`. The rest of the
paper, including its headline theorems, remains open.

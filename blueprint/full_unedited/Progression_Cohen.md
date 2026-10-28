# Progression Cohen identities: checked proof specification

Checkpoint 05, 22 October 2026. Authoritative source: `sources/current/Draft5.tex`,
SHA256 `d2c31b96cb15b00feac09ed4fd9a2b0482726c719c4b772320c0711875d04660`.
The targets are Lemmas **3.11** (`l:progressioncohen`) and **3.12**
(`l:sumoverramanujan`). Both are proved, including the latter's vanishing
and prime-power factorization clauses. This document explains the actual
checked proofs; it does not certify other statements in the paper.

## Statements and source correspondence

Write A_q = (Z/qZ)^×, ψ_q(t)=exp(2πit/q), and

\[
 c_q(n)=\sum_{a\in A_q}\psi_q(na),\qquad
 C_q(n)=\sum_{u\in A_q}c_q(n-u^2).
\]

These are the existing genuine complex exponential definitions in
`QuadraticCohen.lean`. Complete-residue filters and unit-group sums were
already proved equivalent. There is no replacement of these functions by
an assumed closed formula.

All moduli q are positive. The progression modulus g divides q, so g and
h=q/g are positive as well. Lemma 3.12 uses positive y. Inputs b,x,n can
be arbitrary integers, including negative ones.

The congruence r≡b mod g is expressed by the canonical ring homomorphism
ρ_g:ZMod q→ZMod g. In Lean, its divisibility proof is an argument of
`ZMod.castHom`. The paper's gcd(b,g)=1 becomes `IsUnit (b : ZMod g)` or
`IsCoprime (g : ℤ) b`; Mathlib's
`ZMod.coe_int_isUnit_iff_isCoprime` supplies the formal equivalence.
Using an actual unit b in the CRT proof adds no mathematical restriction.

Define

\[
 R_{q,g}(b,n)=\sum_{\substack{r\in A_q\\\rho_g(r)=b}}c_q(n-r).
\]

Lemma 3.11 is

\[
 R_{q,g}(b,n)=
 \begin{cases}
 \mu(h)c_h(n)c_g(n-b),&\gcd(g,h)=1,\\
 0,&\gcd(g,h)>1.
 \end{cases}
\]

The product-modulus theorem takes q=gh with arbitrary positive g,h; this
covers every positive q and divisor g. The divisor/quotient wrappers state
the same result in the paper's notation. Their `NeZero (q/g)` instance only
expresses the positivity already implied by g|q and q>0. The gcd and quotient
instances used for Lemma 3.12 are constructed explicitly in its module.

| Source component | Checked declarations |
|---|---|
| Ordinary Cohen identity used in the proof | `linear_cohen_identity` |
| Genuine Ramanujan sum at a unit equals μ(q) | `ramanujanAtOne_eq_moebius`, `ramanujanSum_unit_eq_moebius` |
| Lemma 3.11, product modulus | `progression_cohen_identity_mul` |
| Lemma 3.11, divisor notation and integer input | `progression_cohen_identity`, `progression_cohen_identity_int` |
| Lemma 3.11, arbitrary modular input | `progression_cohen_identity_residue` |
| Definitions e:mathfraks and e:upsilondef | `principalSquareSum`, `upsilon` |
| Opening the actual normalized sums | `normalized_upsilon_correlation_expansion` |
| Lemma 3.12, equation e:eqjustforLHS | `sum_upsilon_square_identity` |
| Its squarefree vanishing clause | `sum_upsilon_square_eq_zero_of_not_squarefree` |
| Its prime-power factorization clause | `sum_upsilon_square_prime_factorization` |

All declarations are in namespace `PrimeSquares`. The general character-twisted
sum s_χ from e:mathfraksgeneral is not defined or formalized in this checkpoint.
Only the principal-character sum needed for these two lemmas is used.

## 1. Translation of the unit group

The proofs use an elementary fact valid in every commutative ring. If t²=0
and u is a unit, then u+t is a unit with inverse

\[
 u^{-1}-t u^{-2}.
\]

Multiplication verifies this formula using t²=0 and uu⁻¹=1. Translation by
−t is the inverse permutation. Lean constructs the units and both inverse
identities explicitly in `nilpotentAddUnit` and `nilpotentAddEquiv`.

This is an additive translation of units. The earlier quadratic identity
used the different permutation u↦u+t/u. Both are proved from ring identities;
neither presupposes root lifting or any analytic theorem.

## 2. The ordinary linear Cohen identity

First prove c_q(1)=μ(q). At a prime p the existing exact evaluation gives
c_p(1)=−1. At p^(k+2), take t=p^(k+1). Then t²=0 in the residue ring,
but t≠0. Reindexing the unit sum by u↦u+t gives

\[
 c_{p^{k+2}}(1)=\psi_{p^{k+2}}(t)c_{p^{k+2}}(1).
\]

The standard character is injective, so ψ(t)≠1. Therefore the sum is zero.
CRT multiplicativity, together with the proved prime-power evaluations of
the Möbius function, identifies c_q(1) with μ(q) at every positive modulus.
The auxiliary function `ramanujanAtOne` extends this actual sum by zero at
q=0 solely for a natural-number induction interface. Its agreement with
c_q(1) at every positive q is proved.

Multiplication by any unit permutes the unit group, so c_q(a)=μ(q) for unit a.
Now open the two finite sums:

\[
 \begin{aligned}
 \sum_{r\in A_q}c_q(n-r)
 &=\sum_{a\in A_q}\psi_q(na)\sum_{r\in A_q}\psi_q(-ar)\\
 &=\sum_{a\in A_q}\psi_q(na)c_q(-a)
 =\mu(q)c_q(n).
 \end{aligned}
\]

The coefficient −a is again a unit, including for even q. The Lean proof
checks the reordering and phase signs before extracting the common factor.
Modulus one is handled explicitly: it has one unit, its character is
identically one, and μ(1)=1.

## 3. Lemma 3.11: the coprime case

Suppose gcd(g,h)=1 and q=gh. The existing checked CRT equivalence identifies
A_q with A_g×A_h. The progression condition fixes the first coordinate to b;
the second coordinate ranges over all units modulo h. The previously proved
Ramanujan multiplicativity then gives

\[
 R_{q,g}(b,n)=c_g(n-b)\sum_{v\in A_h}c_h(n-v)
 =\mu(h)c_h(n)c_g(n-b).
\]

Lean transports the unit sum by `crtUnitsEquiv`, proves that the canonical
reductions are the two coordinates, evaluates the fixed-coordinate filter,
and applies the ordinary Cohen identity. There is no assumption that the
unscaled standard additive character factors under CRT: the earlier character
scaling proofs establish Ramanujan multiplicativity with the correct phases.

## 4. Lemma 3.11: the shared-prime case

Suppose gcd(g,h)>1. Choose a prime p dividing both, and write g=pℓ, h=pk.
Set t=gk=q/p. Then

\[
 t^2=q\ell k,\qquad g\mid t,\qquad 0<t<q.
\]

Consequently t²=0 in ZMod q, ρ_g(t)=0, and t≠0. Translation by t therefore
permutes precisely the units in the chosen progression class.

For a fixed unit coefficient a in the opened Ramanujan sum, reindexing this
progression-restricted sum multiplies it by ψ_q(−ta). The phase is not one:
injectivity of the character would give ta=0, and a is invertible, forcing
t=0. Thus every such coefficient sum is zero, and so is R_(q,g)(b,n).

`progressionRamanujanSum_eq_zero_of_square_zero` proves the general translation
argument. `progressionRamanujanSum_non_coprime` constructs t with all the
required properties from the shared prime. This branch in fact holds for
any b; coprimality of b is needed only for the nonzero coprime branch.

The argument covers all overlaps, not merely prime-power q. Degenerate cases
g=1, g=q and q=1 enter the coprime branch and require no omitted exception.

## 5. Lemma 3.12: expansion and normalization

Use exactly the definitions in the paper:

\[
 \mathfrak s(a,q)=\frac1{\phi(q)}\sum_{u\in A_q}\psi_q(-au^2),
 \quad
 \Upsilon(a,q,b,y)=\frac{\phi(y)}{\phi([y,q])}
 \sum_{\substack{r\in A_q\\r\equiv b\pmod g}}\psi_q(-ar),
 \quad g=\gcd(q,y).
\]

All three totients φ(q), φ(y), φ([y,q]) are strictly positive. The formal
proof establishes their nonvanishing in ℂ before cancelling the factors.
The product of the three phases is

\[
 \psi_q(-ar)\psi_q(-au^2)\psi_q(ax)=\psi_q(a(x-u^2-r)).
\]

Summing first over a gives the genuine Ramanujan sum, hence

\[
 \frac{\phi(q)\phi([y,q])}{\phi(y)}
 \sum_{a\in A_q}\Upsilon(a,q,b,y)\mathfrak s(a,q)\psi_q(ax)
 =\sum_{u\in A_q}R_{q,g}(b,x-u^2).
\]

Applying the residue-input form of Lemma 3.11 term by term gives exactly

\[
 \mu(h)\mathbf1_{\gcd(g,h)=1}
 \sum_{u\in A_q}c_h(x-u^2)c_g(x-b-u^2),\qquad h=q/g.
\]

The two reductions are explicit ring homomorphisms in Lean. In particular,
the shift in the second factor is x−b−u², with the same sign as the source.

If h is not squarefree, Mathlib's proved Möbius evaluation gives μ(h)=0.
This proves the stated vanishing, without assuming a squarefree-support rule.

## 6. Complete prime-power factorization

If gcd(g,h)=1, CRT also separates the two coordinates of u in the last sum:

\[
 \sum_{u\in A_q}c_h(x-u^2)c_g(x-b-u^2)=C_g(x-b)C_h(x).
\]

`progression_quadratic_correlation_coprime` proves this by the actual CRT
unit equivalence. The earlier prime-power factorization of C and the proved
multiplicativity of μ now give the fully local expression for the normalized
correlation:

\[
 \left(\prod_{p\mid g} C_{p^{v_p(g)}}(x-b)\right)
 \left(\prod_{p\mid h}\mu(p^{v_p(h)})C_{p^{v_p(h)}}(x)\right).
\]

Because q=gh and gcd(g,h)=1, the two prime supports are disjoint and together
cover the prime powers dividing q. Empty products have value one. The local
C factors already have checked evaluations from Lemma 3.1. This completes
the factorization assertion of Lemma 3.12; evaluating and summing the later
Euler products of Lemma 3.14 remains a separate target.

## Verification and limits

The three new modules are `LinearCohen.lean`, `ProgressionCohen.lean` and
`ProgressionCorrelation.lean`. All twelve project modules build. The source
scan and the transitive axiom audit of all 78 named project theorems pass,
allowing only `propext`, `Classical.choice` and `Quot.sound`. No deep analytic
input or additional mathematical axiom is used.

A separate exact-integer experiment checks Lemma 3.11 for every 1≤q≤128,
every divisor g, every unit class b modulo g and every n modulo q: 707,264
cases, including 89,364 cases in the shared-prime branch. There are no
failures. The script uses the classical integer divisor formula for Ramanujan
sums and records an output digest. This is finite experimental evidence;
it is not used to prove any Lean theorem.

The paper's main analytic and application theorems remain open. The formal
results above certify these specified statements, not the complete paper or
all of its exposition. Source-to-formal-statement correspondence must continue
to be reviewed at each milestone.

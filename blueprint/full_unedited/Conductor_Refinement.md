# Lemma 3.27: the complete conductor-sensitive refinement

Checkpoint 12, 22 October 2026. The full statement is proved in Lean by an
alternative elementary argument, including all three estimates, the
logarithmic consequence and the support condition. No extra mathematical
hypothesis is used. The proof actually permits any real character at the
original level; primitivity is unnecessary for this choice of majorant.

The main declaration is `PrimeSquares.conductor_sensitive_refinement` in
`PrimeSquares/ConductorRefinement.lean`. This checkpoint is a proof of this
lemma, not of the paper's headline theorems.

## Source identification and exact scope

The archived `sources/current/Draft5.tex` and its reference map identify:

| Source item | Stable label | Typeset number | PDF page |
|---|---|---|---|
| Previous uniform twisted Gauss bound | `l:Gcharbound` | 3.24 | 22 |
| Current lemma | `l:exceptionalarithmetic` | 3.27 | 23 |
| Three estimates | `e:exceptionalarithmetic` | 3.28 | 23 |
| Support condition | `e:sqfreeconds` | 3.29 | 23 |

Earlier checkpoint 11 prose incorrectly used 3.22 for `l:Gcharbound` and
3.23 for `l:exceptionalarithmetic`. The current reports, inventory and
provenance use the reference-map numbers. The Lean statements were already
tied to the correct stable source labels. No manuscript correction is needed.

Fix a positive integer q₀ and a real Dirichlet character χ₀ modulo q₀. For
each positive integer d, let χ be its actual induced character modulo q₀d,
using Mathlib's `DirichletCharacter.changeLevel`. Write

\[
 s_\chi(a,q)=\frac1{\phi(q)}\sum_{r\in(\mathbb Z/q\mathbb Z)^\times}
       \chi(r)e(-ar^2/q),\qquad
 F_\chi(x,q)=\sum_{a\in(\mathbb Z/q\mathbb Z)^\times}s_\chi(a,q)e(ax/q).
\]

These are the actual definitions `twistedSquareSum` and
`twistedSquareCorrelation`, with the paper's minus sign and totient.
All residue classes x are included; the second estimate requires a unit
coefficient a, exactly as in the paper. Integer inputs are their residue
classes. Modulus one and imprimitive characters are included.

`conductorSigma` is the maximum of the norms over j=0,...,5 and the units
modulo q₀2ʲ. Since multiplication is commutative, these are exactly the
paper's moduli 2ʲq₀. `dyadicTwistNorm` forms the inner finite maximum;
`conductorSigma` forms the outer one. Finite suprema are taken in the
nonnegative reals and then coerced to the reals. The checked lower-bound and
upper-bound lemmas ensure this is the actual maximum, rather than an assumed
upper bound. `conductorRho` and `conductorCorrelationProduct` are exactly

\[
 \rho(d)=\prod_{p\mid d}(1-p^{-1/2})^{-1},\qquad
 G(d)=\prod_{p\mid d}\frac{p+1}{p-1}.
\]

The explicit admissible choice in this proof is

\[
 \mathcal B_0=64\,8^{\omega(q_0)}\sqrt{q_0}.
\]

The combined Lean theorem proves, with an absolute positive constant C,
uniform in q₀, χ₀, d, x and a,

\[
 \mathcal B_0\geq1,\qquad
 |F_{\chi_{q_0d}}(x,q_0d)|\leq\mathcal B_0G(d),
\]
\[
 |s_{\chi_{q_0d}}(a,q_0d)|\leq32\sigma_0d^{-1/2}\rho(d),
 \qquad
 \sigma_0\sqrt{\mathcal B_0}\leq Cq_0^{-1/25},
\]
\[
 (1+\log q_0)\sigma_0\sqrt{\mathcal B_0}\leq C.
\]

If the sum is nonzero for any unit coefficient, it also proves

\[
 d=2^\nu d_1,\quad \nu\leq5,\quad d_1>0,\quad
 d_1\text{ squarefree},\quad(d_1,2q_0)=1.
\]

The natural-number convention makes ν≥0 automatic. For positive d₁,
squarefreeness is the paper's condition μ²(d₁)=1.

The paper's proof proposes the sharper choice
\(\mathcal B_0\asymp\prod_{p\mid q_0,\,p>2}2p/(p-1)\).
That additional comparison is not part of the lemma's statement and is not
claimed here. The larger explicit choice above satisfies every stated
conclusion and avoids real primitive conductor classification. The archived
manuscript has not been edited.

## 1. Real characters and multiplication by squares

For a character on a finite unit group, complex conjugation equals inversion.
Consequently χ has real values if and only if χ²=1, equivalently χ takes
only the values 0, 1 and -1. Lean proves this equivalence in
`dirichletCharacter_quadratic_iff_real`. It also proves that `changeLevel`
preserves the quadratic predicate.

At every unit v, a quadratic character satisfies χ(v²)=1. Thus multiplication
of a unit r by a unit square leaves χ(r) unchanged. This fact supplies the
character invariance needed for the cancellation argument; it is not an
unstated assumption about induced characters.

## 2. A square-preserving shift forces exact cancellation

Let t,s be residues modulo q with

\[
 t^2=s^2=0,\qquad 2s=t,\qquad 2t\ne0.
\]

The existing `squareShiftEquiv` is the unit permutation r↦r+t/r. Its inverse
and the identity

\[
 (r+t/r)^2=r^2+2t
\]

were already checked in `UnitSquareShift.lean`. The new proof shows that

\[
 r+t/r=r(1+s/r^2)^2.
\]

Here 1+s/r² is a unit, with inverse 1-s/r². Thus the permutation also preserves
χ(r) for every quadratic χ. Reindexing the genuine twisted Gauss sum U gives

\[
 U_\chi(a,q)=e(2at/q)U_\chi(a,q).
\]

For a unit a, the additive character is injective and 2at≠0. The phase is
therefore different from one, forcing Uχ(a,q)=0. This is an exact identity,
with no asymptotic input. The normalized sum vanishes as well.

There is also a separate checked parity cancellation: if χ(-1)≠1, then
reindexing by r↦-r gives a zero twisted sum for every coefficient, including
nonunits. The main support proof does not need to classify which local
characters are odd.

## 3. Vanishing at the full modulus

The shift can be applied directly at any modulus q, without first decomposing
χ into local characters.

If an odd prime square p² divides q, write q=p²m and take

\[
 t=pm,\qquad s=\frac{p+1}{2}t\pmod q.
\]

Then pt=0 modulo q, t²=s²=0, and 2s=t. Moreover 0<2pm<p²m, so 2t≠0.

If 64 divides q, write q=64m and take t=16m, s=8m. Again t²=s²=0, 2s=t,
and 2t=32m is nonzero modulo q. Lean checks all divisibility, positivity,
unit and phase conditions, including even moduli in the odd-prime argument.

It follows that a nonzero unit-coefficient sum has

\[
 v_2(q)\leq5,\qquad v_p(q)=1\text{ for every odd }p\mid q.
\]

For q=q₀d, remove the power of two from d to obtain d₁. Its odd prime
exponents are at most one. An odd prime dividing both d₁ and q₀ would have
its square dividing q, a contradiction. This proves the entire support
condition. It holds even for a quadratic character at level q₀d that was not
specified as induced.

## 4. Exact CRT for the induced sums

Let (m,n)=1 and let χ modulo mn be induced from a character χm modulo m.
The unit CRT equivalence sends r to (rm,rn), and the induced character has
value χm(rm). This follows from the actual definition of `changeLevel`.

For a residue a modulo mn, put

\[
 a_m=(a\bmod m)n^{-1}\pmod m,\qquad
 a_n=(a\bmod n)m^{-1}\pmod n.
\]

Both are units when a is a unit. The standard additive character satisfies
the checked CRT identity with these inverse-modulus factors. Finite
reindexing and φ(mn)=φ(m)φ(n) then give

\[
 s_\chi(a,mn)=s_{\chi_m}(a_m,m)s_1(a_n,n).
\]

The inverse coefficients are retained explicitly in
`induced_twistedSquareSum_coprime_mul`; unscaled multiplicativity at a fixed
coefficient is not assumed.

Opening the weighted Fourier sum in the other order gives

\[
 F_\chi(x,q)=\frac1{\phi(q)}
       \sum_{r\in(\mathbb Z/q\mathbb Z)^\times}\chi(r)c_q(x-r^2).
\]

Ramanujan-sum CRT and character induction now give

\[
 F_\chi(x,mn)=F_{\chi_m}(x\bmod m,m)F_1(x\bmod n,n).
\]

There are no inverse factors in x in this latter identity. The Fourier
identity and correlation factorization are proved separately from the
quadratic Gauss factorization.

## 5. The correlation estimate

The earlier unconditional Lemma 3.24 gives the finite bound

\[
 |s_\chi(a,m)|\leq8^{\omega(m)}/\sqrt m.
\]

Summing norms over the φ(m) unit coefficients and using φ(m)≤m yields

\[
 |F_\chi(x,m)|\leq8^{\omega(m)}\sqrt m.
\]

If m=q₀2^ν with ν≤5, then ω(m)≤ω(q₀)+1 and √m≤8√q₀. Hence this is at most
the chosen \(\mathcal B_0\).

If all unit-coefficient sums at q vanish, the correlation is zero. Otherwise
the support theorem supplies d=2^νd₁. Set m=q₀2^ν, n=d₁; they are coprime.
For the principal correlation at the odd squarefree n, the earlier exact
Cohen factors and φ(n)=∏p|n(p-1) give

\[
 |F_1(x,n)|\leq G(n).
\]

Every factor in G is at least one. Since n divides d, G(n)≤G(d). The checked
CRT identity proves the first estimate with constant one.

## 6. The individual-sum estimate

Use the same support decomposition. The norm of the m-part of the CRT product
is bounded by σ₀ by its exact definition. The previous unconditional
principal product bound, with constant four, gives

\[
 |s_1(a_n,n)|\leq \frac4{\sqrt n}
     \prod_{\substack{p\mid n\\p>2}}(1-p^{-1/2})^{-1}.
\]

Each factor of ρ is positive and at least one, so this product is at most
ρ(n)≤ρ(d). Also √d≤8√n. Consequently

\[
 |s_\chi(a,q)|\leq\sigma_0\frac4{\sqrt n}\rho(n)
       \leq32\sigma_0d^{-1/2}\rho(d).
\]

Zero sums are handled explicitly. The proof never divides by σ₀ and thus
includes the σ₀=0 case.

## 7. Decay and the logarithmic consequence

Apply the earlier uniform bound with ε=1/8. Since q₀2ʲ≥q₀ and the exponent
-3/8 is negative, the finite maximum defining σ₀ satisfies

\[
 \sigma_0\leq S q_0^{-3/8}
\]

with an absolute S>0, for every complex χ₀. Put D=8^ω(q₀)≥1. The majorant
satisfies

\[
 \sqrt{\mathcal B_0}=8\sqrt D\,q_0^{1/4}
       \leq8Dq_0^{1/4}.
\]

The already proved elementary prime-factor absorption, used with ε=1/16,
gives D≤Aq₀^(1/16), with an absolute A>0. Multiplication gives

\[
 \sigma_0\sqrt{\mathcal B_0}\leq8SAq_0^{-1/16}
       \leq8SAq_0^{-1/25}.
\]

The comparison uses q₀≥1. No restriction p≡1 (mod 4), prime-distribution
estimate, Weil bound or real-character classification is required for this
alternative choice of majorant.

Finally, the checked elementary logarithm bound gives

\[
 \log q_0\leq25q_0^{1/25},\qquad
 1+\log q_0\leq26q_0^{1/25}.
\]

Multiplying the decay estimate proves the logarithmic conclusion. The
combined theorem takes one positive constant large enough for both
conclusions, before quantifying q₀ and χ₀. Uniformity is therefore part of
the formal statement.

## Files and proof boundary

| Module | Checked role |
|---|---|
| `QuadraticTwistCancellation.lean` | Real/quadratic equivalence, induction, square shift, parity and full-modulus vanishing |
| `TwistedSupport.lean` | Prime exponents and the exact relative support decomposition |
| `InducedTwistCRT.lean` | Actual `changeLevel`, numerator CRT and normalized CRT |
| `TwistedCorrelation.lean` | Actual Fourier sum, Ramanujan identity, induced CRT and finite bound |
| `ConductorFactors.lean` | Exact σ₀ maximum, ρ, G, B₀, positivity and divisor monotonicity |
| `ConductorEstimates.lean` | The first two estimates with constants 1 and 32 |
| `ConductorDecay.lean` | Uniform q₀^(-1/25) decay and logarithmic conclusion |
| `ConductorRefinement.lean` | Full combined source statement, strengthened to all real characters |

All are under `PrimeSquares/`. No proof placeholders or new mathematical
axioms are used. The ordinary Lean foundations `propext`, `Classical.choice`
and `Quot.sound` remain the audit whitelist. Neither Siegel--Walfisz nor PNT
is an input to this lemma. The separate Lemma 3.21 still has its two explicit
PNT-limit hypotheses; their external bridge remains unintegrated.

## Verification and independent experiments

The fresh project build checks all 40 project modules. The transitive axiom
audit covers all 321 named project theorems, including the 49 added here.
The source scan covers 42 Lean files. These are infrastructure counts, not
counts of numbered paper results. Full logs are in `verification/`.

`scripts/check_conductor_refinement.py` uses exact signed integer
polynomials, cyclotomic reduction, integer Ramanujan sums and rational
comparisons. The recorded experiment has zero failures:

| Check | Range | Cases |
|---|---|---:|
| All real characters and all unit coefficients | q=1,...,128 | 452 characters; 16,754 coefficients |
| Higher-power vanishing | Same range | 2,968 |
| Odd-character vanishing, including nonunit coefficients | Same range | 13,937 |
| Explicit shift, square ratio, character invariance and unit permutation | Same range | 2,968 unit cases |
| Relative conductor support | Same range | 723 |
| Fourier identity with source sign | q≤32 | 1,561 |
| Induced Gauss CRT with inverse coefficients | mn≤96 | 20,331 |
| Induced correlation CRT | mn≤96 | 41,144 |
| First estimate with the explicit B₀, checked by squaring | q≤128 | 111,520 |

The induced-level checks include 1,048 pairs of a real base character and a
strictly larger level. The σ₀ estimate and its unbounded uniform decay are
established by Lean, not by a finite numerical claim. These experiments are
independent finite error checks and do not replace the formal proof.

The next dependency stage is the abstract high--low argument in Theorem 4.1
(`t:improvinggeneral`), followed by its application to the prime-square
operators. That work is not part of this checkpoint.

# Lemma 3.24: an unconditional twisted Gauss-sum bound

Checkpoint 11, 22 October 2026. Source label `l:Gcharbound`, equation
`e:Gcharbound`, and the definition `e:mathfraksgeneral`.

The complete statement is now proved in Lean, strengthened from real to all
complex Dirichlet characters. For every epsilon>0 there is C_epsilon>0 such
that for every positive integer q, every Dirichlet character chi modulo q
and every integer a coprime to q,

\[
 |\mathfrak s_\chi(a,q)|
 \le C_\varepsilon q^{-1/2+\varepsilon}.
\]

The constant depends only on epsilon, not on q, chi, a, or the conductor.
No primitive-character assumption is made. This proof uses no PNT input,
unformalized Weil bound, or classification of real characters. The PNT
hypotheses in the separate Lemma 3.21 development are unchanged.

## 1. Source definitions and principal specialization

For a complex Dirichlet character chi modulo q write

\[
 U_\chi(b)=\sum_{r\in\mathbb A_q}\chi(r)e(br^2/q),
 \qquad
 \mathfrak s_\chi(a,q)=\phi(q)^{-1}U_\chi(-a).
\]

`twistedUnitQuadraticGaussSum` and `twistedSquareSum` are exactly these sums,
using the actual modular unit group, the standard complex additive character,
and Mathlib's complex Dirichlet character. The source minus sign and totient
normalization are retained. The principal-character specialization is proved
to equal the previously formalized principal square sum.

Every character value on a unit has norm one, using the checked Mathlib
lemma `DirichletCharacter.unit_norm_eq_one`. The normalized twisted sum
therefore has norm at most one for every coefficient. This also handles
modulus one with its one-element unit group and totient equal to one.

## 2. Count square fibers

Let

\[
 K(q)=\#\{u\in\mathbb A_q:u^2=1\}.
\]

The code defines this as the cardinality of the kernel of the squaring
homomorphism on the genuine modular unit group. For unit a and any residue b,
the fiber of u -> a*u^2 over b has at most K(q) elements. If the fiber is
nonempty, fix v in it. Sending u to u/v injects it into the square kernel:
unit cancellation gives u^2=v^2, hence (u/v)^2=1. This injection is formalized,
including the empty-fiber case, without assuming b is a unit in advance.

## 3. Orthogonality and square scaling

Reindexing r -> v*r for any unit v gives

\[
 \chi(v)U_\chi(av^2)=U_\chi(a),
 \qquad |U_\chi(av^2)|=|U_\chi(a)|.
\]

The code proves the exact complex identity before taking norms. No reality
condition on chi is needed.

Expanding the norm square and summing over every additive frequency gives
the exact finite identity

\[
 \sum_{b\bmod q}|U_\chi(b)|^2
 =q\sum_{\substack{r,s\in\mathbb A_q\\r^2=s^2}}
      \chi(r)\overline{\chi(s)}.
\]

Indeed the inner frequency sum of e(b*(r^2-s^2)/q) is q if the squares agree
and zero otherwise. The additive orthogonality used here was already proved
for the genuine standard character in the earlier Cohen development.
Taking real parts, each character product contributes at most one, and each
r has at most K(q) partners s. Thus the energy E satisfies

\[
 E:=\sum_{b\bmod q}|U_\chi(b)|^2\le q\phi(q)K(q).
\]

The square-scaling orbit has bounded multiplicity by the same fiber lemma.
For a unit a, therefore,

\[
 \phi(q)|U_\chi(a)|^2
 =\sum_{v\in\mathbb A_q}|U_\chi(av^2)|^2
 \le K(q)E
 \le q\phi(q)K(q)^2.
\]

The finite bounded-multiplicity summation inequality is proved separately.
Since phi(q)>0, cancellation and the nonnegative square root give

\[
 |U_\chi(a)|\le K(q)\sqrt q,
 \qquad |\mathfrak s_\chi(a,q)|\le K(q)\sqrt q/\phi(q).
\]

These inequalities are proved for every modulus, character and unit
coefficient in the stated domains, not inferred from numerical tests.

## 4. Modular root counts, including powers of two

At an odd prime power p^j, the unit group is cyclic by the checked Mathlib
theorem `ZMod.isCyclic_units_of_prime_pow`. A finite cyclic group has at most
two solutions to u^2=1, giving K(p^j)<=2.

At powers of two the proof does not assume cyclicity. Exponents j<=2 are
checked by kernel-reduced finite decisions. For j=k+3, the unit 5 modulo
2^(k+3) has order 2^(k+1), by `ZMod.orderOf_five`; its square has order 2^k
and belongs to the range of squaring. Hence that range has at least 2^k
elements. The entire unit group has 4*2^k elements. The exact finite-group
kernel-times-range identity yields K(2^(k+3))<=4. The order, positivity,
range membership, group cardinality and cancellation are all checked in Lean.

The unit CRT equivalence induces an explicit bijection between the square
kernel at mn and the product of the square kernels at coprime positive m,n.
Consequently K(mn)=K(m)K(n). Coprime induction, including q=1, gives

\[
 K(q)\le4^{\omega(q)},
\]

where omega(q) is the cardinality of the actual finite prime-divisor set.
This loose constant is sufficient; the sharper local constant two at odd
primes is also proved. The proof uses CRT for square kernels and does not
postulate a character decomposition of the original exponential sum.

## 5. Totient and epsilon absorption

Euler's exact finite product identity and p<=2*(p-1) for every prime p give

\[
 q\le\phi(q)2^{\omega(q)}.
\]

Combining the proved estimates yields the uniform explicit finite majorant

\[
 |\mathfrak s_\chi(a,q)|\le8^{\omega(q)}q^{-1/2}.
\]

The remaining q^epsilon estimate is elementary. More generally, fix B>=1
and epsilon>0, and take

\[
 N=\left\lceil\exp(\log B/\varepsilon)\right\rceil,
 \qquad A=\exp(N\log B)>0.
\]

There are at most N prime divisors of q not exceeding N. For p>N we have
log B<=epsilon*log p. All logarithms of primes are nonnegative, so the
already proved squarefree-divisor logarithmic budget gives

\[
 \omega(q)\log B
 \le N\log B+\varepsilon\sum_{p\mid q}\log p
 \le N\log B+\varepsilon\log q.
\]

Exponentiating proves B^omega(q)<=A*q^epsilon, uniformly for every positive q.
Applying this with B=8 establishes the full Lemma 3.24. The displayed constant
is effective but intentionally very large; no optimization is claimed.

## Checked declarations and scope

| Component | Lean declaration |
|---|---|
| Actual twisted sum and principal specialization | `twistedSquareSum`, `twistedSquareSum_principal` |
| Square-scaling identity | `twistedUnitQuadraticGaussSum_mul_unit_sq` |
| Square-fiber bound | `unitSquareFiber_card_le` |
| Exact complex energy identity | `twistedGauss_energy_complex` |
| Energy upper bound | `twistedGauss_energy_le` |
| Actual numerator norm bound | `norm_twistedUnitQuadraticGaussSum_le_roots` |
| Odd and dyadic root counts | `unitSquareRootCount_odd_prime_pow`, `unitSquareRootCount_two_pow` |
| Exact CRT for square kernels | `unitSquareRootCount_coprime_mul` |
| Global kernel count | `unitSquareRootCount_le_pow` |
| Elementary totient estimate | `le_totient_mul_two_pow_primeFactors` |
| Fixed prime weights absorbed into q^epsilon | `primeFactor_pow_le_rpow` |
| Explicit 8^omega/sqrt(q) bound | `norm_twistedSquareSum_finite_bound` |
| Full uniform theorem and integer-coefficient form | `twistedSquareSum_uniform_bound`, `twistedSquareSum_uniform_bound_int` |

All declarations are directly in namespace `PrimeSquares`. The final integer
theorem explicitly states epsilon>0, one positive constant, every nonzero
natural modulus q, every complex Dirichlet character and every integer a
coprime to q. Nonzero natural moduli are exactly the positive ones intended
in the source. The exponent is exactly -1/2+epsilon.

No manuscript correction is needed. This completes the general twisted
definition and Lemma 3.24; it does not prove the conductor-sensitive refinements
in Lemma 3.27 or any headline theorem.

## Independent exact checks

`scripts/check_twisted_gauss.py` constructs every character for each q=1,...,32
from exact local unit-group coordinates, including non-real and imprimitive
characters. It uses integer phase counters and reduction modulo cyclotomic
polynomials, with no floating point. It checks multiplicativity, the exact
energy identity, square scaling, fiber bounds, root-count CRT and integer
root/totient inequalities. These finite checks supplement the Lean proofs;
they do not establish an unbounded epsilon estimate by experimentation.

Checkpoint 12 continuation: the full conductor-sensitive Lemma 3.27 is now
proved by the additional support, induced CRT and majorant arguments in
`Conductor_Refinement.md`. This checkpoint 11 exposition describes the
preceding uniform bound.

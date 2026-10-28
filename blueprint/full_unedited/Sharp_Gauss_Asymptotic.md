# Lemma 3.21: sharp bound with an explicit PNT boundary

Checkpoint 10, 22 October 2026. Source label `l:inftyboundsaq`, equation
`e:gaussboundknown`. The complete paper-specific deduction is now proved in
Lean, conditional on the two standard prime-distribution limits below.
The six previously completed numbered results remain unconditional.

## Exact external hypotheses

For real y define

\[
 \theta(y)=\sum_{p\le y}\log p,
 \qquad W(y)=\sum_{p\le y}p^{-1/2},
 \qquad F(y)=\frac{\sqrt y}{\log y}.
\]

In Lean the sums use `Nat.primesLE (Nat.floor y)`. The proof checks the exact
equivalence of membership with p prime and p<=y for the positive cutoffs used.
`PrimeAsymptoticInputs` consists of these two hypotheses, for y tending to
positive infinity through the real numbers:

\[
 \theta(y)/y\longrightarrow1,
 \qquad W(y)/F(y)\longrightarrow2.
\]

Both limits are explicit fields of a proposition supplied to the conditional
theorems. This project does not construct a proof of that proposition. There
are no new `axiom` declarations or proof placeholders. A clean transitive
axiom audit establishes the validity of the implication; it does not establish
the hypotheses.

The second limit is the usual partial-summation consequence of PNT. For
clarity about scope, the bridge from PNT to these two limits is also outside
the present Lean development. Thus the exact formal dependency is this pair
of standard limits, not an imported PNT theorem.

## PNT availability and sources

PNT has been formalized in the separate
[PrimeNumberTheorem+ project](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd).
The pinned Mathlib's `docs/100.yaml`, entry 5, links to it, and a targeted
source inspection found no PNT asymptotic to import from our pinned Mathlib.
The upstream project inspected on 22 October 2026 targets Lean/Mathlib 4.35.0;
our existing verified development targets Lean 4.34.1 and Mathlib commit
`d13f23b723b8a846827a245b89c10fc7d3f11612`. No upgrade, external import, or
external-project axiom audit has been performed. This is an unintegrated
dependency, not a claim that PNT has never been formalized. See
`verification/pnt-availability.json` for the inspected file hashes.

A published reference is Iwaniec--Kowalski, *Analytic Number Theory*, AMS
Colloquium Publications 53, the paper's existing bibliography key `iwaniec`.
The classical PNT and its original sources are also recorded in
[NIST DLMF 27.2, equation 27.2.3](https://dlmf.nist.gov/27.2#E3).
The following elementary bridge explains precisely why the hypotheses are
standard PNT consequences; it is a mathematical explanation, not a Lean proof.
Writing pi(y) for the prime counting function, partial summation gives

\[
 \theta(y)=\pi(y)\log y-\int_2^y\frac{\pi(t)}t\,dt,
 \qquad
 W(y)=\frac{\pi(y)}{\sqrt y}
       +\frac12\int_2^y\frac{\pi(t)}{t^{3/2}}\,dt.
\]

PNT says pi(y)~y/log y. The first integral is O(y/log y)=o(y), by splitting
at sqrt(y) and using pi(t)=O(t/log t). In the second formula the integral is
asymptotic to `2*sqrt(y)/log(y)`: replace pi(t) by t/log t above an arbitrarily
large fixed lower endpoint, and compare derivatives of the integral with
`2*sqrt(y)/log(y)`. Its derivative ratio tends to one. The finite initial
interval contributes a bounded constant. These formulas give the two limits.

## 1. Logarithmic budget, proved without PNT

Let q>=1, S be its prime divisors, and L=log(q). The squarefree product of
these prime divisors divides q, so

\[
 \sum_{p\in S}\log p\le L.
\]

`primeFactors_log_budget` proves this using the actual natural prime-factor
set, positive products, divisibility, and monotonicity of the real logarithm.

## 2. Finite threshold inequality, proved without PNT

For every real y>=2,

\[
 \sum_{p\in S}p^{-1/2}
 \le W(y)+\frac{L-\theta(y)}{\sqrt y\log y}.
\]

Put c=1/(sqrt(y)*log(y)) and subtract c*log(p) from each summand. Since
sqrt(t)*log(t) increases on t>=1, the difference is nonnegative below y and
nonpositive above y. Drop the nonpositive terms, extend the small terms to
all primes <=y, and apply the logarithmic budget. The general finite-set
comparison and its application are both proved in `PrimeFactorEstimates.lean`.
No exact extremizer or prime-factor asymptotic is assumed.

## 3. Reciprocal and logarithmic corrections, proved without PNT

For L>=2,

\[
 \sum_{p\in S}p^{-1}\le1+\log L+1/\log2.
\]

For p<=L, enlarge the sum to the harmonic sum through floor(L). For p>L,
use `1/p <= (1/L)*(log p/log 2)` and the same logarithmic budget. This proof
also covers nonsquarefree q. It deliberately uses a sufficient O(log L)
bound; the stronger O(log log L) in the source is unnecessary for 3.21.

Writing A(p)=(1-p^(-1/2))^(-1), the project proves, for every integer p>=2,

\[
 A(p)\le4,
 \qquad \log A(p)\le p^{-1/2}+4/p.
\]

Indeed `log A <= A-1`, and the exact geometric identity is
`A-1 = p^(-1/2) + A/p`. The local bound, the identity, and summation over the
actual odd prime factors are all checked by Lean.

## 4. Connect the actual Gauss sums

Checkpoint 09 proved the genuine normalized square-sum estimate

\[
 |\mathfrak s(a,q)|\le q^{-1/2}\,4\prod_{p\mid q,\ p>2}A(p)
 \quad ((a,q)=1).
\]

For y>=2 put

\[
 E(y)=\log4+4(1+\log y+1/\log2),
 \quad
 B(y)=W(y)+\frac{y-\theta(y)}{\sqrt y\log y}+E(y).
\]

The finite proofs give, unconditionally when L>=2,

\[
 \log\left(4\prod_{p\mid q,\ p>2}A(p)\right)\le B(L),
 \qquad |\mathfrak s(a,q)|\le q^{-1/2}e^{B(L)}.
\]

Under the explicit analytic hypotheses,

\[
 \frac{B(y)}{F(y)}
 =\frac{W(y)}{F(y)}+1-\frac{\theta(y)}y+\frac{E(y)}{F(y)}
 \longrightarrow2.
\]

The identity is proved for y>1 using sqrt(y)^2=y. The final correction tends
to zero by the checked Mathlib limits `(log y)^j/sqrt(y) -> 0`, j=1,2.
The fixed constant four at two is therefore absorbed rather than omitted.

## 5. Full source statement and quantifiers

Define the explicit coefficient error

\[
 r(q)=B(\log q)/F(\log q)-2.
\]

`gaussAsymptoticError_tendsto` proves r(q)->0 under the two analytic inputs.
`principalSquareSum_sharp_error_bound` proves the inequality with exponent
`(2+r(q))*F(log q)` without those inputs. The theorem
`principalSquareSum_two_add_o_one` combines these into the literal source
statement, with one r independent of the integer coefficient a.

`principalSquareSum_sharp_bound_int` also states the equivalent epsilon form:
for every epsilon>0 there exists an integer Q such that for every positive
q>=Q and every integer a coprime to q,

\[
 |\mathfrak s(a,q)|\le q^{-1/2}
 \exp\!\left((2+\varepsilon)
 \frac{\sqrt{\log q}}{\log\log q}\right).
\]

`principalSquareSum_three_bound_int` proves the coefficient-three consequence
by choosing epsilon=1. The threshold is existential, as in the source;
no effective numerical value is claimed. Modulus zero is excluded explicitly
by `NeZero q`. The reciprocal square root is the source's q^(-1/2), and the
integer-to-unit equivalence is the same checked one used in checkpoint 09.

There is no new manuscript correction at this checkpoint. No headline theorem
or real-character-twisted Gauss bound is claimed proved.

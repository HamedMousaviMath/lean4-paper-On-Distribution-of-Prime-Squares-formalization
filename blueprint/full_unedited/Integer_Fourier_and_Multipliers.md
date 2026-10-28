# Integer Fourier transform and the actual square multipliers

Checkpoint 22. Source: Draft5, equations `e:basicaverages` and
`e:tildedef2`, and the Fourier framework preceding Lemma 6.5. This unit
connects the completed actual averaging operators to Mathlib's genuine
Plancherel theory. It supplies prerequisites for Proposition 4.19; it does
not prove its major-arc, low, high, error or maximal estimates.

## Exact conventions

Let T = R/Z with Haar measure of total mass one. Put

\[
 c_n(\theta)=\exp(-2\pi i n\theta),\qquad n\in\mathbb Z.
\]

Mathlib's `fourier n` uses the positive phase. We explicitly define
`negativeFourierCharacter n = fourier (-n)` at period one. The theorem
`negativeFourierCharacter_real` proves the displayed exponential formula
for every real lift theta. The character product law and unit magnitude
are proved without restricting theta to rational frequencies.

The measure is `AddCircle.haarAddCircle`, not an unspecified volume
normalization. Elements of circle L2 are equivalence classes modulo
almost-everywhere equality. All formulas involving their chosen
representatives are correctly stated almost everywhere.

## The actual unitary transform

Mathlib proves that its Fourier monomials form an orthonormal Hilbert
basis. Negation is a bijection on the integers, so the family c_n has the
same orthonormality and the same dense span. We prove these facts and
construct `negativeFourierBasis` using `HilbertBasis.mk`.

Inverting the basis representation defines the complex-linear isometric
equivalence

\[
 \mathcal F:\ell^2(\mathbb Z;\mathbb C)\simeq L^2(T;\mathbb C).
\]

Consequently, for every actual l2 sequence f, rather than only finite
inputs,

\[
 \|\mathcal Ff\|_2=\|f\|_2.
\]

This is `integerFourier_norm`. The inverse is part of the constructed
isometric equivalence; `integerFourier_inverse` records one inverse
identity. No Plancherel assumption, postulate or finite-grid approximation
is used. The pinned Mathlib supplies the underlying density and Hilbert
space arguments.

The inverse coefficients have the required positive inverse phase:

\[
 (\mathcal F^{-1}g)(n)
 =\operatorname{fourierCoeff}(g)(-n)
 =\int_T e(n\theta)g(\theta)\,d\theta.
\]

`integerFourier_coefficient` proves the coefficient identity, using the
actual Mathlib coefficient definition and the reflected Hilbert basis.

For the finite sequence supported on F with coefficients f(n), we prove

\[
 \mathcal F\!\left(\sum_{n\in F} f(n)\delta_n\right)
 =\left[\theta\mapsto\sum_{n\in F} f(n)e(-n\theta)\right]_{L^2}.
\]

This is `integerFourier_finiteInput`. The continuous polynomial's exact
real-lift formula is `finiteFourierPolynomial_real`; its squared L2 norm
is exactly the finite sum of |f(n)|^2, by
`finiteFourierPolynomial_parseval`. Empty support and zero coefficients
are included.

## Continuous symbols and all-input operator bounds

For a continuous symbol m on T, the product m g is in circle L2 for every
g in circle L2, since

\[
 |m(\theta)g(\theta)|\leq\|m\|_\infty |g(\theta)|.
\]

We prove membership, representative compatibility, complex linearity and
continuity, constructing `circleMultiply m`. Define

\[
 U_m=\mathcal F^{-1}\,\operatorname{Mul}_m\,\mathcal F.
\]

`integerMultiplier m` is this actual continuous complex-linear map on
integer l2. We prove

\[
 \|U_m\|\leq\|m\|_\infty,
 \qquad
 \mathcal F(U_mf)=m\mathcal Ff\quad\hbox{a.e.}
\]

The operator bound holds for every l2 input. Addition, scalar
multiplication, zero, negation and subtraction of symbols have the exact
corresponding operator identities. In particular, if B >= 0 and
|m(theta)-v(theta)| <= B for every theta, then

\[
 \|U_m-U_v\|_{\ell^2\to\ell^2}\leq B.
\]

`integerMultiplier_error_bound` proves this implication. The uniform
symbol inequality is an explicit hypothesis of that transport lemma.
It is not an assertion that the paper's proposed approximation already
satisfies it. This unit treats continuous symbols; it makes no claim to
have implemented every bounded measurable multiplier or a maximal
multiplier theorem.

## Translations and weighted square sums

Let tau_d f(x) = f(x-d). First we prove exactly

\[
 \tau_d\delta_n=\delta_{n+d}.
\]

Multiplying c_n by c_d gives c_{n+d}. The transform identity therefore
holds on every single-coordinate input. Equality of continuous linear
maps follows from density of finite-support l2 sequences, via
`lp.ext_continuousLinearMap`. Thus

\[
 \tau_d=U_{c_d},\qquad
 \mathcal F(\tau_df)(\theta)=e(-d\theta)\mathcal Ff(\theta)
 \quad\hbox{a.e.}
\]

The equality is `integerTranslate_l2_multiplier`, and the representative
formula is `integerFourier_translate_ae`. This step checks the sign
against the actual translation definition; it does not change that
definition to fit a desired multiplier.

For any finite set S of natural numbers, real scalar c and real weights w,
put

\[
 T_{S,c,w}f(x)=c\sum_{n\in S}w(n)f(x-n^2),\qquad
 m_{S,c,w}(\theta)=c\sum_{n\in S}w(n)e(-n^2\theta).
\]

`finiteSquareSymbol_real` proves this symbol's real-lift formula, and
`finiteSquareOperator_l2_multiplier` proves

\[
 T_{S,c,w}=U_{m_{S,c,w}}.
\]

Finite linear combinations of the proved translation identities give
this equality. It holds on all of integer l2, for arbitrary signs of c
and w, including empty S. No distribution-of-primes input is involved.

The full and annular symbols specialize to

\[
 \widehat A_{N,w}(\theta)=\frac1N\sum_{0<n\leq N}w(n)e(-n^2\theta),\qquad
 \widehat{\widetilde A}_{N,w}(\theta)
 =\frac1N\sum_{\lfloor N/2\rfloor<n\leq N}w(n)e(-n^2\theta).
\]

The exact operator equalities are
`weightedSquareAverage_l2_multiplier` and
`annularWeightedSquareAverage_l2_multiplier`. The two von Mangoldt
real-lift formulas explicitly use `ArithmeticFunction.vonMangoldt`.
Every prime power remains in the sum. The formal definitions also cover
N=0, using Lean's total inverse 0^-1=0; the source application uses
positive dyadic N.

The theorem `annularWeightedSquareAverage_fourier_error_bound` now turns
any future proved uniform error estimate for the actual annular symbol
into the same l2 operator bound. The hard estimate itself remains open.

## Inverse kernels and convolution agreement

For a continuous m, define the genuine l2 sequence

\[
 K_m=\mathcal F^{-1}[m]_{L^2}.
\]

`fourierKernel_coefficient` identifies K_m(x) with the actual coefficient
`fourierCoeff m (-x)`. Using the already proved translation identity,
commutativity of symbol multiplication gives

\[
 U_m(z\delta_i)(x)=K_m(x-i)z.
\]

Finite summation then proves

\[
 U_m\!\left(\sum_{i\in F}f(i)\delta_i\right)(x)
 =\sum_{i\in F}K_m(x-i)f(i)
\]

for every finite F, every complex coefficient function f and every integer
x. These are actual pointwise integer-sequence equalities, not just circle
a.e. statements. They supply `KernelL2Bound K_m ||m||` and its version with
any proved uniform bound B. For the finite square symbol, the new inverse
kernel is proved equal at every integer to the original
`finiteSquareKernel`. Thus both constructions agree exactly.

A general smooth-cutoff inverse kernel need not have the original
averaging kernel's compact support. No positivity, compact support or
absolute summability is inferred for general K_m by this unit.

## Rational frequencies and the earlier Gauss sums

For every positive modulus q and all integer a,n, we prove

\[
 c_n(a/q)=\operatorname{stdAddChar}_{q}(-an).
\]

The squared version gives

\[
 e(-an^2/q)=\operatorname{stdAddChar}_{q}(-a n^2).
\]

These are `negativeFourierCharacter_rational` and
`negativeSquareCharacter_rational`. The proof uses the actual complex
exponential definitions, without a coprimality restriction on a.

The earlier principal and twisted quadratic sums therefore equal,
respectively,

\[
 \frac1{\varphi(q)}\sum_{u\in(\mathbb Z/q\mathbb Z)^\times}
   c_{\widetilde u^2}(a/q),\qquad
 \frac1{\varphi(q)}\sum_{u\in(\mathbb Z/q\mathbb Z)^\times}
   \chi(u)c_{\widetilde u^2}(a/q),
\]

where tilde u is the standard natural representative. Both identities
are formally proved, for arbitrary complex Dirichlet characters in the
twisted case, and include q=1. They connect the arithmetic modules' minus
sign and totient normalization to the analytic symbols.

## Files and verification scope

| Module | New named theorems | Result |
|---|---:|---|
| CircleFourier.lean | 15 | Reflected Hilbert basis, actual unitary transform, finite formulas and Parseval |
| CircleMultipliers.lean | 21 | Actual all-input multiplier maps, norm bounds and linear identities |
| SquareFourier.lean | 16 | Exact translations, full/annular square symbols and error-bound transport |
| FourierKernels.lean | 9 | Actual inverse kernels, finite convolution and genuine kernel l2 bounds |
| FourierGaussCompatibility.lean | 4 | Rational phase, principal and twisted normalization compatibility |

The five modules add 65 named theorems, for 678 in the whole project.
The total includes supporting lemmas; it is not a count of completed
numbered paper statements. Every module is root-imported and every named
theorem is included exactly once in the transitive axiom audit.

The full fresh artifact-cache-disabled build passes 3595 jobs, including
every one of the 80 project modules and the root, with no warnings/errors.
All 678 named project theorems pass the complete transitive whitelist:
propext, Classical.choice and Quot.sound. The source scan checks 82 Lean
files and finds no placeholders or extra mathematical axioms. Lean 4.34.1
and Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612 remain pinned.

## Independent finite probes

`scripts/check_fourier_conventions.py` uses exact Gaussian rationals and
formal independent log(prime) symbols. It checks 532 translations, 2856
actual finite square multiplier identities, 189 dyadic symbol
reconstructions, 7 Gauss sign/normalization cases and 27 finite cyclic
Parseval cases. The rational frequency denominators are 1,2,4. No floating
point or sampling tolerance is used.

At theta=1/4 the explicit diagnostics include

\[
 \mathcal F\delta_1=-i,\qquad
 \widehat A_{4,1}=(1-i)/2,\qquad
 \widehat A_{4,\Lambda}=(2\log2-i\log3)/4.
\]

The annular von Mangoldt value is (log2-i log3)/4. Reversing the sign
changes -i to +i, and omitting the prime power 4 loses log2/4 from the
full symbol. Both mutations are detected. These finite probes do not
prove general Plancherel or any asymptotic estimate. The genuine
infinite-dimensional bridge is the separate Lean construction above.

## What remains before Proposition 4.19

| Dependency | Status |
|---|---|
| Actual averages, positivity, elementary local and uniform lp/l2 bounds | Complete at checkpoint 21 |
| Actual negative-phase Fourier/Plancherel and exact square multipliers | Complete in this unit |
| Published deep analytic input boundaries | Must be verified and stated before use |
| Lemma 6.5: actual major-arc prime-square input and paper-specific bookkeeping | Open |
| Lemma 6.9: actual approximation by V_N | Open |
| Proposition 6.14: low contribution | Open |
| Lemma 6.16 and Orlicz prefix estimate | Open |
| Proposition 6.21: high and maximal high estimates | Open |
| Proposition 4.19 assembly and Theorem 1.1 application | Open |

The next step is Lemma 6.5: exact residue grouping of the actual finite
Lambda sum, non-unit and prime-power bookkeeping, partial summation,
and consumption of precisely quantified published analytic inputs.
Own-paper deductions remain proof obligations. Exceptional conductor,
character and beta may vary with N and must not be fixed across scales
in later maximal arguments.

The ten completed numbered results remain unchanged. This unit introduces
no new deep hypothesis. Lemma 3.21 still has its earlier two explicit PNT
limits; their external bridge is not integrated and is not used here.
The frozen manuscript and accepted revisions are unchanged.

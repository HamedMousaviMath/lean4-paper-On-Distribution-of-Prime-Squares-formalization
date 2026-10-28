# The source densities, oscillatory integrals and conditional major-arc deduction

Checkpoint 26. This unit specializes the proved Abel identity and quantitative
error transport to the manuscript's actual power model. All derivatives,
continuity and integrability requirements are discharged. A bound on the
genuine unweighted progression prefix remains an explicit hypothesis.

## Exact source objects

For an integer N>=1, a real frequency theta and beta>0, write

\[
 g_\theta(t)=\exp(-2\pi i\theta t^2),\qquad
 C_{q,r}(x)=\sum_{0\leq n\leq\lfloor x\rfloor}
       \mathbf1_{n\equiv r\pmod q}\Lambda(n).
\]

The Lean prefix includes n=0, whose von Mangoldt coefficient is zero.
It includes every prime power. The lower endpoint in the integral is the
real number N/2. The corresponding finite sum uses the natural floor
N/2, with that correspondence explicitly proved in the Abel calculation.
The statements therefore also cover odd N; dyadic N is not required here.

Define the complex progression model and density by

\[
 H_{q,z,\beta}(t)=\frac1{\phi(q)}
       \left(t-z\frac{t^\beta}{\beta}\right),\qquad
 D_{q,z,\beta}(t)=\frac1{\phi(q)}(1-zt^{\beta-1}).
\]

The new Lean definitions are `progressionPowerModel` and
`progressionPowerDensity`. The primitive is `exceptionalPrimitive`.
All real quantities are explicitly embedded into the complex numbers
where needed. These are actual functions, rather than unspecified model
parameters supplied with regularity assumptions.

The normalized oscillatory integral is

\[
 M_{N,\beta}(\theta)=\frac1N\int_{N/2}^{N}
       t^{\beta-1}g_\theta(t)\,dt.
\]

`annularOscillatoryModel` initially uses the Bochner integral over
(N/2,N]. `annularOscillatoryModel_interval` identifies it with the
interval integral in the manuscript's equation e:M. That identity also
holds at N=0 with Lean's inverse convention, although subsequent
estimates require N>=1. The integral parameter theta is real: the phase
is not assumed periodic in theta when t is nonintegral.

Two calibration results are proved. At beta=1 the real power disappears,
and at beta=1, theta=0 the model has value exactly 1/2 for N>=1. This
checks the annular interval length and the factor 1/N together.

## Derivative and integrability

For t>0 and beta>0, Mathlib's derivative of the real power gives

\[
 \frac{d}{dt}\frac{t^\beta}{\beta}
 =\frac{\beta t^{\beta-1}}{\beta}=t^{\beta-1}.
\]

Positivity of beta justifies cancellation; positivity of t avoids the
singularity at zero. Applying the complex embedding, subtraction and
constant-multiple derivative rules proves H'=D. Every point in
[N/2,N] is positive when N>=1, so this proves all the regularity needed
by the previously established integration-by-parts theorem.

Continuity of the real power on this positive interval gives continuity
and interval integrability of D. Continuity of both the power and the
quadratic phase proves integrability of their product. Integrability
is proved before distributing the Bochner integral over subtraction.
The calculus only requires beta>0; the manuscript's additional beta<=1
can be imposed when applying it to an exceptional zero.

Distributing the actual density integral then proves

\[
 \frac1N\int_{N/2}^{N}g_\theta(t)D_{q,z,\beta}(t)\,dt
 =\frac1{\phi(q)}
       \bigl(M_{N,1}(\theta)-zM_{N,\beta}(\theta)\bigr).
\]

This is `progressionPowerDensity_integral`.

## Exact residue error and its quantitative bound

Let

\[
 W_{q,r}=\sum_{N/2<n\leq N\atop n\equiv r\pmod q}
       \Lambda(n)g_\theta(n),\qquad
 E(t)=C_{q,r}(t)-H_{q,z,\beta}(t).
\]

The exact identity `annularProgressionPowerModel_error_identity` is

\[
 \frac{W_{q,r}}N
 -\frac{M_{N,1}(\theta)-zM_{N,\beta}(\theta)}{\phi(q)}
 =\frac1N\left(g_\theta(N)E(N)-g_\theta(N/2)E(N/2)
       -\int_{N/2}^{N}g'_\theta(t)E(t)\,dt\right).
\]

There is no assumed residue estimate in this identity. Both endpoint
terms and the exact derivative integral are present. All model regularity
conditions have been proved for the displayed H and D.

Suppose delta>=0 and, throughout the actual real interval [N/2,N],

\[
 |C_{q,r}(t)-H_{q,z,\beta}(t)|\leq N\delta.
\]

The previously proved derivative bound and exact normalization imply

\[
 \left|\frac{W_{q,r}}N
 -\frac{M_{N,1}(\theta)-zM_{N,\beta}(\theta)}{\phi(q)}\right|
 \leq\delta\bigl(2+4\pi|\theta|N^2\bigr).
\]

This is `annularProgressionPowerModel_error_bound`. The term 2 records
both endpoints. The N in the raw prefix error cancels against the
normalizing 1/N. No derivative or integrability hypothesis remains for
the model in this bound.

## Gauss sums and the actual annular symbol

Let q>=1, let chi be a complex Dirichlet character modulo q, and let
kappa be a complex coefficient. Assume the displayed raw prefix bound
holds for every reduced residue r with z=kappa*chi(r), using the same
beta, chi, kappa and delta throughout this one interval. Define

\[
 U(N,q)=\frac{\log q+2\sqrt N\log N}{N}.
\]

The earlier exact finite residue grouping, proved nonunit contribution
bound and Gauss-sum identity now give

\[
 \begin{aligned}
 \big|\widehat{\widetilde A}_{N,\Lambda}(a/q+\theta)
 &-\big(\mathfrak s(a,q)M_{N,1}(\theta)
       -\mathfrak s_\chi(a,q)\kappa M_{N,\beta}(\theta)\big)\big|\\
 &\leq U(N,q)+\phi(q)\delta(2+4\pi|\theta|N^2).
 \end{aligned}
\]

This is `annularMangoldt_majorArc_from_prefix_bound`. Its symbol is the
actual finite von Mangoldt annular Fourier sum, not an abstract surrogate.
The Gauss sums use the manuscript's negative phase and division by phi(q).
The proof sums the per-residue errors over exactly phi(q) units. The
nonunit error U(N,q) is already proved for the actual coefficients.

Taking kappa=0 omits the exceptional term; taking kappa=1 includes it.
`annularMangoldt_ordinary_from_prefix_bound` separately gives the ordinary
case directly from a prefix bound around t/phi(q), with no exceptional
parameter in the statement. The deduction does not require primitivity
of chi or coprimality of a and q; a published analytic input may impose
those additional hypotheses. Exceptional data may change with N. The
theorem makes no claim that the same data work at different scales.

## Source correspondence and remaining analytic work

This verifies the power-model differentiation, actual partial summation
and Gauss-sum substitution in the proof of Lemma 6.5, after equation e:M.
It does not prove or silently assume the manuscript's raw progression
distribution estimate. To use a published theorem as an explicit deep
input, its primary-source statement, range, exceptional data and uniformity
must first be matched to the displayed prefix hypothesis.

The final conversion to O(R^-5), with the stated N,Q,R range and choice
of constants, remains open. The independent prime-square minor-arc
estimate also remains open. Thus full Lemma 6.5, Proposition 4.19 and
the headline applications are not marked complete. No new PNT bridge,
Siegel-Walfisz theorem or Landau-Page theorem is asserted here.

## Files

| Module | New named theorems | Result |
|---|---:|---|
| ExceptionalProgressionDensity.lean | 12 | Actual model derivative, continuity and integrability, source interval identity, normalization and density integral |
| PrimeSquarePartialSummation.lean | 4 | Exact source-model error, quantitative residue bound and conditional ordinary/exceptional major-arc deductions |

No numerical experiment is used to justify these analytic statements.
They are checked Lean proofs with the raw prefix-error bound displayed
as a hypothesis where it is needed.

<!-- checkpoint-verification -->

## Verification

All 90 project modules and the root were freshly rebuilt: 3605 jobs pass without warnings/errors. All 739 named theorems pass the complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound. The source scan checks 92 Lean files. Exact unique import/audit coverage and unchanged frozen source hashes are checked before packaging. There are no placeholders or added mathematical axioms.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. No new deep analytic input or own-paper lemma is assumed.

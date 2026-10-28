# Weighted upper main term: complete conditional proof

This file concerns the source lemma `l:wumatomakisum`, with alpha=9/8. The checked endpoint is `goldbach_weighted_upper_main_term_complete`. For every A>0, every fixed C>=A+24, and every eta>0, it gives one threshold in N such that the source inequality holds for every n=12 modulo24 with N^2(log N)^(-A)<=n<N^2. Its coefficient is c_alpha W(alpha)+eta, where c_alpha=16 exp(-gamma/2)/sqrt(pi alpha). This is the uniform epsilon formulation of the source o(1).

The theorem uses the actual finite multiplier set, source Euler products, smoothed singular integrals, and lower main term. No weighted-prime sum, error-absorption conclusion, or Goldbach main-term comparison is an independent hypothesis.

## Independent inputs

Four general interfaces remain explicit theorem parameters: `ClassicalHalfMeanValueInput`, `ClassicalPrimeLogMertens`, `ClassicalPrimeMertensRatios`, and the existing `GoldbachClassicalIntervalMertens`. The first is the nonnegative strongly multiplicative upper corollary of the corrected Tenenbaum effective mean theorem, with uniform constants and its prime-balance condition stated explicitly. The others contain ordinary fixed-progression Mertens estimates. Their exact scope and the external corollary reductions are recorded in `docs/EXTERNAL_WEIGHTED_MEAN_INPUTS.md`. They are hypotheses, not new Lean axioms. Their truth is not asserted by this project.

## Arithmetic normalization

The source multiplier ell=2up has a unique pair (u,p): the primes dividing u are 1 modulo4 and p is 3 modulo4. Lean proves the finite image identity and uniqueness, including the lower prime endpoint p=z. The geometry gives R<z_ell, u<z_ell<p, and N^2/ell>=2 for all source pairs once R<N^(2/9).

For every odd prime p>3, the joint factor U_p is positive. The associated strongly multiplicative weight h_R has nonnegative prime values at most6. The small-prime cancellation identities are proved even when an individual arithmetic factor vanishes. They yield the exact normalizations

\[
X_n\Theta_n(z)=3C_R(n)H_{1,R}(n)V_3(R,z),
\]

and

\[
X_n(2up)\Theta_{n,2up}(z_{2up})
=6B_R(n)\frac{h_R(u)}{2up}H_{2up,R}(n-1)V_0(R,z_{2up}).
\]

Here V_3 and V_0 are the actual finite outer Euler products. The positive factors satisfy B_R<=C_R. These are equalities in the original definitions, not asymptotic replacements.

## The varying multiplicative weight

Above R the prime values of h_R equal the fixed 1 modulo4 baseline (p-1)/(p-2). The finite perturbation below R and the classical logarithmic prime sums give, uniformly in n and y>=R,

\[
\left|\sum_{p\le y}(h_R(p)-1/2)\frac{\log p}{p}\right|
\le 6\log R+10K_0.
\]

The application of the independent effective mean theorem is proved from this bound. The finite Euler product is exactly C_R/B_R times an ordinary 1 modulo4 product. Thus, with kappa=exp(-gamma/2)/sqrt(pi), the ordinary partial sum is at most

\[
(\kappa+K\varepsilon^\delta)(1+K_1/\log R)
\frac{C_R(n)}{B_R(n)}\frac{x}{\sqrt{\log R\log x}}
\]

under the explicit scale and prime-balance budgets. Constants K,delta precede R,n,x,epsilon. At R=(log N)^C and a=exp(sqrt(log N)), Lean proves every budget eventually, uniformly in n.

The small denominators do not require this sharp mean estimate. A coarser instance applies beyond R^D for a fixed D>1. Below that scale a finite Euler-product bound applies; above it a checked Abel identity applies. Together they give

\[
\sum_{u\le a}\frac{h_R(u)}u
\le\frac{C_R(n)}{B_R(n)}
\left(P(\log R)^6+A'\frac{1+\log a}{\log R}\right),
\]

with constants independent of R,n,a. After multiplication by the prime reciprocal and kernel bounds this range is negligible on the required scale.

## The double weighted sum and W

Two finite Abel estimates are proved with their derivatives, signs, integrability, floor conventions, and boundary terms. The denominator summation is bounded using the preceding mean. Finite variable-interval integration interchanges its order with the prime sum. The prime sum uses the 3 modulo4 logarithmic Mertens estimate. The possible prime p=z contributes at most 1/(z(log z)^2); its remaining error is at most 2(2K_0+1)/(log z)^3.

At D=2 log N, the logarithmic variables r=log(2u)/D and v=log p/D give the actual source region. The two changes of variables are checked, and

\[
\int_0^{1/9}\frac{dr}{\sqrt r}
\int_{4/9}^{(1-r)/2}\frac{dv}{v(1-r-v)^2}
=8\sqrt2\,\mathcal W(9/8).
\]

The endpoint at r=0 is integrable. Replacing log u by log(2u) costs at most sqrt(1+log2/log a), which tends to one. The small-denominator, prime, and Abel boundary coefficients all tend to zero. Choosing epsilon arbitrarily small therefore proves, uniformly in n, the sharp fixed kernel bound with coefficient kappa W(9/8)+eta. A checked logarithmic-loss argument proves the same bound for every m in the entire retained interval N^2(log N)^(-A_1)<=m<=N^2.

## Integration, smoothing, and relative errors

The finite sum of original Archimedean integrals is interchanged exactly with integration. On the retained region the logarithmic kernel bound is compared directly with the defining integrand of H_1(n): log(n-y^2)<=2 log N. No assertion about an unrestricted real power of log m near m=0, or a relative shift H_1(n-1)/H_1(n), is needed.

The discarded set has measure at most 2T/sqrt(n). The actual reciprocal mass over pairs is at most M(log N)^7. The already proved singular-integral smoothing bound is uniform in the multiplier, so its total error is also controlled by that mass. The lower bound for H_1(n) on the retained n range is proved internally.

For A_1=A+14 and C>=A+24, both total errors are bounded relative to the common positive quantity

\[
S=C_R(n)H_1(n)\sqrt{\log R/\log N}.
\]

The discarded-region contribution is at most [768 M/(log2)^3](log N)^(-3) S, and the total smoothing contribution at most 48 M K (log N)^(-2) S. The lower smoothing error is at most 8K_s/log N times H_1(n). All three coefficients tend to zero with thresholds independent of n.

## Final comparison

The full Mertens ratio and log z_ell=one-quarter log(N^2/ell) give the upper coefficient 48(kappa W+o(1)) multiplying S. The exact lower normalization and half Mertens ratio give the lower coefficient 3 sqrt(9/8)+o(1). The identity 3 sqrt(alpha)c_alpha=48 kappa is checked. A positive-tolerance continuity argument concludes the original uniform source inequality.

The theorem statement needs no replacement. Two proof passages are supplied separately in `docs/WEIGHTED_UPPER_MAIN_TERM_REPLACEMENTS.tex`: the non-strict lower endpoint p>=z, and Step6 with its retained cutoff and direct H_1(n) comparison. The selected manuscript is unchanged.

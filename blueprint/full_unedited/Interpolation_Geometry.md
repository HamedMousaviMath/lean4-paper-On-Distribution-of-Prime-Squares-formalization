# Corollary 4.15: uniform geometric weights and actual complex block bounds

Current checkpoint 20: the full abstract Corollary 4.15 is complete,
including strong interior interpolation and p=2. This document records an
earlier stage; see [Strong_Improving_Complete.md](Strong_Improving_Complete.md)
for the completed proof and current scope.


Checkpoint 19 update: actual rank blocks, coefficient mass and the strong
finite bilinear estimate are now proved. See `Rank_Blocks_and_Finite_Bilinear.md`.
The remaining-obligation list below records checkpoint 18; output norm
duality and final strong operator assembly still remain open.

Checkpoint 18 proves the actual geometric summation estimate needed for
strong interpolation, its exact N scaling, and the estimate for any
specified finite family of complex convolution blocks. Two modules add
22 named theorems. **The full strong interior estimate in Corollary 4.15
remains open:** the rank partition and its coefficient mass bound, finite
duality, and final assembly are still required.

## Source and checked scope

Source: Corollary 4.15 (`c:improvinggeneral`), near line 2431 of
`sources/current/Draft5.tex`. Equation 4.17, the global restricted estimate,
and the strong p=2 case are already proved. The target equation 4.16 is

\[
 \|A_N f\|_{p'}+\|B_N f\|_{p'}
 \le C_p N^{1/p'-1/p}\|f\|_p,
 \qquad p_0<p\le2,
 \qquad p_0=\frac{2(s+r)}{2r+s}.
\]

Fix p0<q<p<2. For one kernel K, the available global restricted bound has
constant A, and its genuine continuous l2 realization has norm <=B. Put

\[
 a=\frac1q-\frac1p>0,\qquad b=\frac1p-\frac12>0.
\]

`interpolation_gaps_pos` proves these strict inequalities. The geometric
module works for arbitrary a,b>0 and A,B>=0. No prime distribution input
is used by this deduction.

| Module | Named theorems | Checked content |
|---|---:|---|
| `InterpolationGeometry.lean` | 15 | Actual weights, summability, uniform total sum, actual Schur estimates |
| `InterpolationBlockBounds.lean` | 7 | Exact scaling, complex block bound, finite family estimate |

## The actual summable weight

For X>0 and n>=0, define

\[
 h_X(n)=\min\left\{A\left(\frac{2^n}{X}\right)^a,
                   B\left(\frac{2^n}{X}\right)^{-b}\right\}.
\]

This is the Lean definition `interpolationWeight`. The proved constant is

\[
 C(A,B,a,b)=\frac{A}{1-2^{-a}}
             +\frac{2^b B}{1-2^{-b}}.
\]

`interpolationWeightConstant_nonneg` proves C>=0. Both geometric ratios
are strictly between zero and one by `dyadic_decay_ratio`.

First, summability itself follows for every X>0 from

\[
 0\le h_X(n)\le B X^b(2^{-b})^n.
\]

The factorization and comparison are proved, then the checked Mathlib
geometric-series theorem gives `interpolationWeight_summable`. This initial
majorant depends on X; the next argument removes that dependence.

For X>=1, construct k>=0 with 2^k<=X<2^(k+1), using the checked
Archimedean power-selection theorem. For n<k,

\[
 h_X(n)\le A(2^{-a})^{k-n}.
\]

The map n->k-n is injective on {0,...,k-1}. Therefore this finite sum is
bounded by the full nonnegative geometric series A/(1-2^(-a)). This
argument is checked in `finite_reversed_geometric_sum_le`; truncation of
natural subtraction is handled using the explicit range condition.

For the tail, indexed by n+k with n>=0, X<=2*2^k gives

\[
 h_X(n+k)\le 2^b B(2^{-b})^n.
\]

The negative power reverses the ratio comparison, with positivity proved
before applying it. Summing the tail yields 2^b*B/(1-2^(-b)). The original
convergent series is exactly its finite head plus this shifted tail.

For 0<X<1, take k=0. The head is empty, and X<=2*2^0 supplies the same
tail estimate. No assertion 2^k<=X is used in this case.

Thus `interpolationWeight_tsum_le` proves, for every real X>0,

\[
 \sum_{n\ge0}h_X(n)\le C(A,B,a,b).
\]

The constant contains no X or N. `interpolationWeight_N_squared` gives
the actual application X=N^2 for every real N>0, including N<1.

## Schur with the actual weights

For any finite index sets S,T, the matrix w(i,j)=h_(N^2)(i+j) has finite
row and column sums <=C. The earlier injective-shift lemma bounds each
row by the now-proved total series. The finite Schur theorem therefore
applies without an additional summability or geometric-bound hypothesis.

`interpolationWeight_finite_schur` proves the coefficient l2 estimate.
`interpolationWeight_finite_schur_lp` gives, for 1<=P<=2,

\[
 \sum_{i\in S,j\in T}h_{N^2}(i+j)c_i d_j
 \le C\left(\sum_{i\in S}|c_i|^P\right)^{1/P}
       \left(\sum_{j\in T}|d_j|^P\right)^{1/P}.
\]

The formal exponent is ENNReal P, with ordinary value P.toReal. Empty
sets, zero weights/constants and signed real coefficients are included.

## Exact scale algebra

`interpolation_scale_balance` proves, for N,f,g>0 and arbitrary real x,y,

\[
 N^{1-2x}f^xg^x
 =N^{1-2y}f^yg^y\left(\frac{fg}{N^2}\right)^{x-y}.
\]

The proof expands the quotient and product powers, then combines powers
of positive bases. Specializing f=2^i, g=2^j gives the dyadic identity.

For nonnegative amplitude bounds u,v, put

\[
 c_i=2^{i/p}u,\qquad d_j=2^{j/p}v.
\]

The Lean definition `interpolationBlockCoefficient` uses (2^i)^(1/p),
and `dyadic_pow_rpow` justifies interchange of the natural and real powers.
The restricted and l2 block scalars satisfy the exact identities

\[
 uv A N^{1-2/q}2^{i/q}2^{j/q}
 =N^{1-2/p}c_i d_j A
   \left(\frac{2^{i+j}}{N^2}\right)^a,
\]

\[
 uv B 2^{i/2}2^{j/2}
 =N^{1-2/p}c_i d_j B
   \left(\frac{2^{i+j}}{N^2}\right)^{-b}.
\]

`interpolation_block_min_identity` factors their minimum as
N^(1-2/p)*c_i*d_j*h_(N^2)(i+j). Its common factor is nonnegative, including
zero amplitudes. The previously proved `holderConjugate_scaling` identifies
1-2/p with the paper's 1/p'-1/p when p>1.

## Actual complex convolution blocks and finite families

Suppose |F|<=2^i, |G|<=2^j, |f|<=u on F and |g|<=v on G, with u,v>=0.
`finiteKernelPairing_dyadic_block_bound` proves for the actual finite
sesquilinear convolution pairing

\[
 |B_{F,G}(f,g)|
 \le N^{1-2/p}c_i d_j h_{N^2}(i+j).
\]

Its input is the already available restricted indicator bound at q,
positivity of K, and a genuine continuous l2 realization with norm <=B.
The l2 pairing estimate is derived from that actual operator. Monotonicity
of positive powers gives the dyadic cardinality bounds. The checked
positive-kernel extension handles all complex phases. The minimum identity
above then gives the literal scale factor, without dropping powers of N.

`finite_complex_block_family_bound` sums these actual complex pairings over
any specified finite families F_i,G_j with their support-cardinality and
amplitude bounds. Triangle inequality and the actual-weight Schur estimate
give

\[
 \left|\sum_{i\in S,j\in T}B_{F_i,G_j}(f_i,g_j)\right|
 \le N^{1-2/p} C
       \left(\sum_{i\in S}|c_i|^p\right)^{1/p}
       \left(\sum_{j\in T}|d_j|^p\right)^{1/p}.
\]

The constants depend on A,B,p,q and not on N or the number of blocks. The
generic theorem takes the restricted bound and genuine l2 bound as explicit
inputs, along with the stated finite block data. The restricted bound is
already proved from the paper's abstract high-low inputs in checkpoint 16.
No partition or desired coefficient mass estimate is silently supplied.

## What remains before closing the corollary

The finite family estimate does not yet compare its coefficient norms
with those of arbitrary original inputs. The next steps are:

1. Construct the decreasing-magnitude dyadic rank blocks for every finite
   complex input, prove coverage/disjointness, and prove sum c_i^p<=3 sum
   |f|^p, including ties, zero input, and first/last blocks.
2. Identify the original finite bilinear pairing with the sum over these
   actual blocks and apply `finite_complex_block_family_bound`.
3. Prove finite-output lp norm duality with the correct complex phase,
   converting the finite bilinear estimate to the finite-input norm bound.
4. Apply the already checked lp realization and exact-constant density
   transfer, retain the two operators' l2 constants, and assemble the strong
   interior range with p=2.

Corollary 4.15 remains partial until these connections are complete. Its
desired conclusion is not an axiom or external analytic hypothesis.

## Verification and finite experiments

All 64 project modules and the root receive a fresh build with the artifact
cache disabled: 3461 jobs pass without warnings or errors. All 511 named
theorems pass the transitive axiom audit, allowing only propext,
Classical.choice and Quot.sound. The source audit scans 66 Lean files.
No new mathematical axiom or deep analytic input is used.

`scripts/check_interpolation_geometry.py` independently checks 2592 finite
96-term geometric sums, enclosing 248832 terms. The six positive exponents
include 1/16, and eight N values range from 1/16 to 2^20. Zero constants,
N=1 and both sides of that scale are included. Fractional powers have
certified rational enclosures of width at most 2^(-40): each root enclosure
is checked by exact integer/rational powers. The finite sum is bounded
from above and its proposed constant from below before comparison. No
floating-point arithmetic or tolerance is used.

The script also checks 19440 block-minimum identities exactly with rational
powers of two, including 8505 zero-amplitude cases. All pass. These finite
experiments do not establish the infinite series theorem; Lean proves that
theorem for all allowed parameters. They do not verify the remaining rank
construction, duality, full strong corollary or prime-square operator inputs.

The nine completely proved unconditional numbered paper results remain
unchanged. Lemma 3.21 retains its earlier explicit PNT limits independently.
The archived manuscript and accepted revision fragments are unchanged;
no new manuscript correction has been established.

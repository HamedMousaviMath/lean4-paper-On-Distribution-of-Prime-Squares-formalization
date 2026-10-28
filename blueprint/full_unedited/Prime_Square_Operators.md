# Actual prime-square operators and annular reconstruction

Checkpoint 21 constructs the source's actual von Mangoldt and ordinary
square averages, proves their elementary operator inputs, and proves the
exact annular identities and dyadic reconstruction. Five modules add
48 named theorems. All 75 modules and the root have a fresh clean build
(3482 jobs); all 613 named theorems pass the transitive axiom audit, and
77 Lean files pass the source scan.

**Proposition 4.19 is still open.** Its Fourier low, high, error and maximal
estimates are not proved or assumed in these new results. No headline
prime-square application is counted as complete. The abstract Theorem 4.1
and full abstract Corollary 4.15 remain complete.

## Source definitions and domains

The source averages are equation `e:basicaverages`, near line 993 of
`sources/current/Draft5.tex`:

\[
 A_{N,w}f(x)=\frac1N\sum_{0<n\le N}w(n)f(x-n^2).
\]

The two weights are w(n)=1 and Mathlib's actual
ArithmeticFunction.vonMangoldt. In particular, Lambda(p^j)=log(p) for
every j>=1. Prime powers are retained. Replacing Lambda by a sum over
primes alone would change the source operator.

N is the arithmetic cutoff; the spatial scale is N^2. The formal
definitions take N:Nat, which includes all dyadic scales in Proposition
4.19. The elementary uniform norm theorems apply to every N>0. The
definitions also have a total N=0 extension, giving zero operators;
the source's positive-scale statements do not rely on that extension.

For every finite sequence-space exponent P with 1<=P and p=P.toReal>0,
weightedSquareAverage hp N w is a genuine continuous complex-linear map
lp(P)->lp(P). Its underlying coordinate expression is precisely the
displayed sum. The annular definition is

\[
 \widetilde A_{N,w}f(x)=\frac1N\sum_{N/2<n\le N}w(n)f(x-n^2),
\]

using natural integer division for N/2. This is the source's
`e:tildedef2` at dyadic scales. No finite-support restriction on f is
imposed on either continuous operator.

## Constructing the actual operators and kernels

integerTranslate hp d sends f(x) to f(x-d). Its membership in lp follows
by reindexing the summable norm powers through the integer translation
bijection. Reindexing the norm sum proves exact norm preservation.
The map is complex-linear and continuous with operator norm at most one.

For a finite S:Finset Nat and a real normalizer c, define

\[
 T_{S,c,w}=c\sum_{n\in S}w(n)\tau_{n^2},\qquad
 K_{S,c,w}(z)=c\sum_{n\in S}\mathbf1_{z=n^2}w(n).
\]

finiteSquareOperator and finiteSquareKernel are these actual objects,
with real coefficients embedded in the complex scalars. The norm bound

\[
 \|T_{S,c,w}\|\le |c|\sum_{n\in S}|w(n)|
\]

follows from the triangle inequality and the translation norm bound.
For c>=0 and nonnegative weights this is at most c*sum w(n).

The proof natSquare_int_injective checks injectivity of n->n^2 from
nonnegative natural indices into the integers. Consequently the kernel
at m^2 is c*w(m) when m belongs to S and is zero otherwise. It is zero
outside the finite image of S. Positive coefficients give a nonnegative
real-valued kernel, and coefficientwise domination gives kernel domination.

finiteSquareKernel_finiteInput proves the exact identity with the existing
finiteConvolution for every finite set and arbitrary complex coefficients.
It interchanges the two finite sums and uses
x-y=n^2 iff y=x-n^2. Thus the continuous maps agree with actual convolution;
they are not unrelated maps with only a scalar norm model.

| Module | New named theorems | Checked role |
|---|---:|---|
| FiniteSquareOperators.lean | 8 | Genuine lp translations, coordinates and finite operator norm |
| SquareAverageKernels.lean | 12 | Actual kernel, finite convolution, positivity, support and local bound |
| WeightedSquareAverages.lean | 10 | Full/annular definitions, normalization, mass and spatial scale |
| PrimeSquareAverages.lean | 10 | Actual Lambda, elementary Chebyshev bound and source elementary inputs |
| DyadicSquareReconstruction.lean | 8 | Exact half subtraction, telescoping, reindexing and both bottom terms |

## Uniform norms without a PNT assumption

Mathlib's pinned Chebyshev theorem psi_le_const_mul_self proves

\[
 \sum_{0<n\le N}\Lambda(n)=\psi(N)
 \le (\log4+4)N.
\]

The equality of the sums, including their endpoint conventions, is checked
in mangoldt_square_mass_bound. It uses the natural-floor identity at N.
This is an elementary upper bound already proved in Mathlib, not an
unformalized PNT input. Put C_Lambda=log4+4>0.

The actual full and annular operator norms are at most C_Lambda for
Lambda and at most one for ordinary squares, uniformly over N>0 and
every finite p>=1. The annular mass is bounded by the full mass because
its index set is a subset and the weights are nonnegative. Normalizing
by 1/N gives the bounds. In particular, the actual kernels satisfy the
existing genuine KernelL2Bound definition with constants C_Lambda and 1.

These are bounds on each operator, uniform in N. They do **not** assert
an l2 bound for the supremum over N. Proposition 4.19's maximal high
estimate remains a separate open theorem.

## Positivity, domination and the local spatial bound

For S contained in (0,N], the kernel vanishes outside [1,N^2] in the
integers. The support theorem proves this from the actual square indices;
it is not a support assumption.

Use the finite window W_N(x)=[x-N^2,x] intersected with the integers.
The kernel support gives the exact localization

\[
 (K*\mathbf1_F)(x)=(K*\mathbf1_{F\cap W_N(x)})(x).
\]

Injectivity of the square indices and the ordinary coefficient 1/N then give

\[
 |\widetilde A_{N,\mathbb N^2}\mathbf1_F(x)|
 \le N^{-1}\|\mathbf1_{F\cap W_N(x)}\|_1
 =(N^2)^{-1/2}\|\mathbf1_{F\cap W_N(x)}\|_1.
\]

The equality of scale factors is proved in square_inverse_spatial_scale.
The one-sided window is smaller than the source's symmetric window;
the estimate supplies the indicator-local bound used by HighLowEndpointInputs.

Mathlib proves 0<=Lambda(n)<=log(n). Since 0<n<=N, logarithm monotonicity
gives Lambda(n)<=log(N). Both actual kernels are positive, so summing
coefficientwise domination proves

\[
 |\widetilde A_{N,\Lambda}\mathbf1_F(x)|
 \le\log N\,\widetilde A_{N,\mathbb N^2}\mathbf1_F(x)
 \le\log(N^2)\,\widetilde A_{N,\mathbb N^2}\mathbf1_F(x).
\]

The last comparison is used at spatial scale N^2 with source a=1.
These are the indicator versions consumed by the already checked
abstract theorem. The structure AnnularSquareElementaryInputs packages
both positive kernels, domination, localization bound and two genuine l2
bounds. annular_square_elementary_inputs constructs it for every N>0;
none of its fields is an unproved assumption.

## Exact annular difference and dyadic reconstruction

For every natural M and arbitrary real weight w, the actual continuous maps obey

\[
 \widetilde A_{2M,w}=A_{2M,w}-\tfrac12 A_{M,w}.
\]

The proof splits (0,2M] into (0,M] and (M,2M], then checks the normalizers
(1/2)*(1/M)=1/(2M), including M=0 in the total extension. There is no
unjustified replacement of floor(N/2) by N/2 for odd N.

The base scale is A_(1,w)=w(1)*tau_1. Induction proves the weighted
telescoping identity for N=2^k. Normalizing and reflecting the finite
index range gives the source's descending order:

\[
 A_{2^k,w}
 =\frac{w(1)}{2^k}\tau_1
  +\sum_{j=0}^{k-1}2^{-j}\widetilde A_{2^{k-j},w}.
\]

The sum is empty at k=0. The complex scalar coefficients are exactly
the real dyadic coefficients embedded in C. The reflection and coefficient
cancellation are checked, using nonvanishing of powers of two.

For Lambda, Mathlib proves Lambda(1)=0, so the bottom term vanishes.
For ordinary squares, w(1)=1, so it is N^-1*f(x-1). The final declarations
mangoldtSquareAverage_dyadic_reconstruction and
ordinarySquareAverage_dyadic_reconstruction match the source formulas
`e:annularreconstruction` and the following square-average identity.
These are equalities of actual continuous maps, not only identities for
indicators or finite coefficient arrays.

## Remaining Proposition 4.19 dependencies

The source correspondence below distinguishes completed prerequisites
from unproved conclusions. No listed open own-paper lemma is treated as
a deep published theorem or assumed in the new Lean results.

| Source | Dependency and remaining work |
|---|---|
| e:basicaverages, e:tildedef2, e:annularaverages, e:annularreconstruction | Actual definitions and operator identities now checked |
| Elementary hypotheses in the proof of Theorem 1.1 | Positivity, indicator domination/localization and genuine uniform l2 bounds now checked at N^2 |
| Lemma 6.5, l:prime-square-input | Open: exact annular Fourier sums, non-unit/prime-power bookkeeping, residue grouping and partial summation; published Landau--Page and minor-arc inputs need precise boundaries before use |
| Lemma 6.9, l:aaplemma | Open: actual major-arc model, separation, complementary range, approximation error and its Fourier-to-l2 bridge |
| Proposition 6.14, p:lowcontribution | Open: actual smooth low multiplier, inverse-transform decay, ordinary/exceptional arithmetic assembly and local maximal average |
| Lemma 6.16, l:notBourgain, and c:orlicz-prefix | Open: own-paper multifrequency and prefix estimates; no blanket transference or maximal assumption introduced |
| Proposition 6.21, p:highupperbound | Open: high and maximal high estimates, actual Gauss/conductor bounds, and exceptional characters varying with scale |
| Proposition 4.19, p:decompositionofan | Open: construct and join the low/high/error operators and every stated bound; elementary averages alone do not prove it |
| Theorem 1.1, t:improvingfixed | Open: apply the checked abstract theorems after the actual decompositions, then connect the annular endpoint and the general cutoff |

The existing arithmetic results remain available. Lemma 3.21's sharp
asymptotic still has its two earlier explicit PNT-limit hypotheses; any
future consumption must retain that boundary. It is not used in this
checkpoint's Chebyshev norm proof.

The next coherent unit is the genuine integer Fourier/Plancherel bridge
and the exact finite multiplier identities. The pinned Mathlib source
Mathlib.Analysis.Fourier.AddCircle already contains a Fourier Hilbert
basis and Parseval infrastructure, but it has not yet been imported or
connected here. Its basis uses the positive phase, while the paper's
transform uses e(-n*theta); the index/sign must be explicitly matched.

For later maximal bounds, q0, beta and the exceptional character are
scale-dependent in Lemma 6.5. They must not be silently frozen across N.
The low term's exceptional cutoff d<=Q/B0 and the complementary high
terms must retain both the conductor and current-scale restrictions.
The actual low and high kernels need not have the compact support of
the original averaging kernel.

## Verification and independent exact experiments

All 75 project modules and the root were freshly compiled with the artifact
cache disabled: 3482 jobs pass without warnings or errors. Every one of
the 613 named project theorems passes the complete transitive axiom audit,
allowing only propext, Classical.choice and Quot.sound. The source scan
checks 77 Lean files with no placeholders or added mathematical axioms.
Exact import/module and unique theorem/audit coverage were checked, as
were all frozen source hashes. No Lean source changed after these checks.

scripts/check_square_averages.py uses rational coefficients of formal
log(prime) symbols and exact Gaussian rational arithmetic; no floating
point is used. It checks 1542 support cases, 1028 positivity cases,
387 annular difference identities, 39 ascending and 39 descending dyadic
reconstructions through arithmetic cutoff 4096, 11256 complex finite
convolution identities, 14280 local indicator bounds and 184 translation
norm cases at exponents two and four. All pass.

Three diagnostics detect changed conventions: omitting prime powers loses
log(2)/4 at shift 16 for N=4; omitting the ordinary-square bottom term
loses 1/4 at shift one for N=4; using the half subtraction at odd N=3
incorrectly leaves -1/6 at shift one. The last diagnostic is outside the
source's dyadic hypothesis and is not a manuscript error.

The experiment checks finite identities and elementary probes, not
Chebyshev's analytic inequality, the full operator norm, a Fourier
estimate or Proposition 4.19. Those current general elementary norm
statements are Lean proofs. Exact ranges, digests and limitations are
in verification/square-averages-numerical.json. The source manuscript
and accepted revisions are unchanged; no new source edit is pending.

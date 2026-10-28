# Corollary 4.15: checked interpolation foundations

Current checkpoint 20: the full abstract Corollary 4.15 is complete,
including strong interior interpolation and p=2. This document records an
earlier stage; see [Strong_Improving_Complete.md](Strong_Improving_Complete.md)
for the completed proof and current scope.


Checkpoint 18 update: the actual geometric weight bound, exact N scaling,
and actual complex block/family estimates are now proved; see
`Interpolation_Geometry.md`. The remaining-obligation list below records
checkpoint 17. Rank construction, coefficient mass, finite-output duality
and final strong assembly still remain open.

Checkpoint 17 proves four supporting modules with 32 named theorems. These
complete the operator-realization and density infrastructure, the finite
complex-input bridge, and the finite weighted Schur estimate. **The strong
interior estimate in Corollary 4.15 is still open.** In particular, the
coarse bound below has no improving power of N.

## Source correspondence

The source is Corollary 4.15 (`c:improvinggeneral`), near line 2431 of
`sources/current/Draft5.tex`. Its equation 4.16 asks for

\[
 \|A_Nf\|_{p'}+\|B_Nf\|_{p'}
 \le C_p N^{1/p'-1/p}\|f\|_p,
 \qquad \frac{2(s+r)}{2r+s}<p\le2.
\]

Theorem 4.1, the global finite-indicator estimate 4.17, actual restricted
weak distribution bounds, and the strong p=2 case were already proved.
This checkpoint supplies genuine sequence-space constructions needed for a
direct global proof of the remaining interpolation step. It does not invoke
the interpolation theorem cited by the paper as an external input.

| Module | Named theorems | Checked content |
|---|---:|---|
| `LpInclusion.lean` | 5 | Contractive continuous complex-linear inclusions for finite 1<=P<=Q |
| `FiniteComplexInputs.lean` | 11 | Finite inputs and norms, actual convolution identity, complex positivity bound |
| `LpRealizations.lean` | 10 | Coarse lp realizations, uniqueness, extension of finite norm estimates by density |
| `FiniteSchur.lean` | 6 | Weighted Cauchy--Schwarz, Schur, Hankel sums, finite lp coefficient bounds |

P and Q in the Lean declarations are ENNReal exponents, with their ordinary
finite values P.toReal and Q.toReal. The spaces use counting measure on Z,
represented by Mathlib's actual `lp`, not a norm formula on an arbitrary
function. The Schur and inclusion lemmas also allow other index types.

## Contractive inclusions

`lp_inclusion_norm` proves that the canonical inclusion from lp to lq has
norm at most one whenever 1<=P<=Q<infinity. Membership comes from
`Memℓp.of_exponent_ge`; the new proof establishes the norm inequality.

Writing p=P.toReal and q=Q.toReal, for every finite S it proves

\[
 \sum_{i\in S}|f_i|^q
 =\sum_{i\in S}|f_i|^{q-p}|f_i|^p
 \le \|f\|_p^{q-p}\sum_{i\in S}|f_i|^p
 \le \|f\|_p^q.
\]

The coordinate bound |f_i|<=||f||p and p-summability are already checked
Mathlib results. The lp norm criterion converts the finite-sum estimates
into the claimed q norm bound. Real-power identities are justified with
q>0, including zero coordinates, the zero vector and P=Q. The inclusion is
then packaged as `lpInclusion`, an actual continuous complex-linear map.
Its operator norm is proved <=1 and its coordinates are unchanged.

## Finite complex inputs and positivity

`finiteInputLp F f P` is the actual finite sum

\[
 \sum_{y\in F} f(y)e_y.
\]

It equals f on F and zero outside F. Its exact norm is proved for every
positive finite real exponent. Truncating an lp sequence to F does not
increase its norm. No support, phase or nonzero coefficient is assumed.

For an l2 operator T agreeing with the kernel on finite indicators,
`kernelL2_realization_single` proves T(z e_y)(x)=K(x-y)z by complex
linearity. `kernelL2_realization_finiteInput` then proves

\[
 T\bigl(\textstyle\sum_{y\in F}f(y)e_y\bigr)(x)
 =\sum_{y\in F}K(x-y)f(y).
\]

Thus arbitrary complex coefficients refer to the same operator as the
previous indicator estimates. This is an exact identity for every x.

For a nonnegative real kernel represented in C, define the actual finite
sesquilinear pairing

\[
 B_{F,G}(f,g)=\sum_{x\in G}\sum_{y\in F}
 K(x-y)f(y)\overline{g(x)}.
\]

`finiteKernelPairing_bound_by_indicators` proves

\[
 |B_{F,G}(f,g)|\le A B
 \left|\langle T\mathbf1_F,\mathbf1_G\rangle\right|
\]

when |f(y)|<=A on F and |g(x)|<=B on G, with nonnegative amplitude
bounds. Triangle inequality controls the phases. Positivity identifies the
sum of absolute kernel coefficients with the original indicator pairing.
Empty sets and zero amplitudes are included.

## A genuine operator on the required sequence spaces

For 1<=P<=2<=Q<infinity, `lpL2Lift` is the composition

\[
 \ell^P\hookrightarrow\ell^2
 \xrightarrow{\ T\ }\ell^2\hookrightarrow\ell^Q.
\]

Both inclusions are proved contractions, so its norm is <=||T||. It agrees
with the explicit finite convolution for every finite complex input.
`kernelLpBound_of_l2` packages the coarse bound with its indicator
agreement. `kernelLp_realization_unique` proves that two continuous
complex-linear maps agreeing on the kernel indicators coincide, using
their agreement on coordinate vectors and density.

Taking P=p and Q=p' gives the spaces required by the corollary for 1<p<=2.
The generic formal theorem has the explicit exponent inequalities P<=2<=Q.
This only supplies a coarse bound. Since 1/p'-1/p<0 for p<2, it cannot by
itself provide the required decay as N grows.

`lp_bound_of_finiteInputs` proves a separate density implication. If a
continuous lp-to-lq map has norm bound D on all actual finite inputs, it has
the same bound on every lp input. The proof uses the norm-convergent net of
finite sums from `lp.hasSum_single`, continuity, and preservation of a
nonstrict inequality under limits. `lp_opNorm_bound_of_finiteInputs` gives
the operator-norm formulation for D>=0. The finite-input estimate is a
hypothesis of this generic transfer lemma; its interpolation application
remains to be proved, and is not assumed in a final paper theorem.

## Weighted Schur, without a support-size loss

For finite S,T, nonnegative weights w(i,j), and any real coefficients c,d,
`finite_weighted_schur` proves

\[
 \sum_{i\in S,j\in T}w_{ij}c_i d_j
 \le C\Bigl(\sum_{i\in S}c_i^2\Bigr)^{1/2}
       \Bigl(\sum_{j\in T}d_j^2\Bigr)^{1/2},
\]

provided all row and column sums are <=C, with C>=0. Weighted
Cauchy--Schwarz is proved by applying ordinary finite Cauchy--Schwarz to
sqrt(w)c and sqrt(w)d. The row and column estimates bound the two weighted
energies. Square-root identities complete the bound, including C=0.

`finite_hankel_row_sum_le` proves that a finite row of h(i+j) is bounded
by sum h when h is nonnegative and summable. The indexing shift is injective,
so no term is counted twice. `finite_hankel_schur` supplies the corresponding
matrix estimate. These generic statements require summability and the
total-sum bound; those conditions for the proposed interpolation weight
are **not yet proved**.

`finite_energy_le_lp` uses the contractive counting-space inclusion to
prove the finite l2 coefficient norm is <= its lp norm for 1<=P<=2.
`finite_weighted_schur_lp` therefore replaces the two coefficient l2
norms by their lp norms, with the same C. The bound is independent of the
number of blocks. No dyadic decomposition is assumed in these statements.

## Remaining obligations

The complete strong corollary still needs these connections:

1. Construct a decreasing-magnitude partition of every finite complex
   input into dyadic rank blocks, proving their cardinalities and lp mass
   bound, including first, last, empty and tied-value cases.
2. From the two actual indicator estimates, derive the block estimate
   with its exact N scaling. Prove the proposed geometric weight is
   summable with a bound uniform in every positive N.
3. Apply the checked complex positivity and Schur estimates to that
   actual partition and weight. This must yield a genuine finite bilinear
   lp bound, without an unproved decomposition hypothesis.
4. Prove finite-output lp duality with the correct complex phase. Convert
   the finite bilinear estimate to the finite-input output norm bound.
5. Apply the checked realization and density lemmas, retain both l2
   constants, and assemble the interior range with the existing p=2 case.

Only then can Corollary 4.15 be marked complete. A successful global route
would make the paper's interval-localization step unnecessary for this
deduction; no such completed global interpolation theorem is claimed yet.

## Verification and exact finite probes

All 62 modules and the root receive a fresh build with the artifact cache
disabled. All 489 named project theorems are checked by the transitive axiom
audit; only propext, Classical.choice and Quot.sound are allowed. There are
no new mathematical axioms, proof placeholders or deep analytic inputs.
The declaration-discovery scanner now ignores comments and strings, after
the audit caught a comment sentence being mistaken for a theorem name.

The deterministic script `scripts/check_interpolation_foundations.py` uses
only integers and exact fractions. It records zero failures in 98304 finite
complex positive-kernel pairing cases, 160012 vector-pair Schur checks on
259 matrices, and 3410 lp inclusion checks at integer exponents. Empty sets,
zero amplitudes, zero weights, signed coefficients and equality cases are
included. It also probes the proposed dyadic weights at 63 parameter
choices, including 0<N<1, with 1008 row and 504 Schur checks. Counts are
experiment cases; restricted inputs may repeat across cases.

These experiments do not prove the unbounded geometric estimate, sorting,
duality or full interpolation. They do not verify the later prime-square
operator hypotheses. The general supporting implications above are Lean
proofs. Full archived sources and accepted revisions are unchanged. The
count of completely proved unconditional numbered results remains nine;
Lemma 3.21 retains its earlier explicit PNT hypotheses independently.

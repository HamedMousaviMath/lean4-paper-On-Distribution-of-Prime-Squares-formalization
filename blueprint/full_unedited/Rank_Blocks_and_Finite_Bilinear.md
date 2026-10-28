# Corollary 4.15: constructed rank blocks and the finite bilinear estimate

Current checkpoint 20: the full abstract Corollary 4.15 is complete,
including strong interior interpolation and p=2. This document records an
earlier stage; see [Strong_Improving_Complete.md](Strong_Improving_Complete.md)
for the completed proof and current scope.


Checkpoint 19 constructs the dyadic rank decomposition for every finite
complex input and proves its coefficient mass estimate. It then proves
the strong finite bilinear estimate with the exact N scaling. Three modules
add 40 named theorems. **The full strong operator corollary remains partial:**
finite-output norm duality and final assembly are still required.

## Source correspondence and inputs

The source is Corollary 4.15 (`c:improvinggeneral`), near line 2431 of
`sources/current/Draft5.tex`. Fix p0<q<p<2, where
p0=2(s+r)/(2r+s). The previously proved global equation 4.17 supplies

\[
 |\langle T\mathbf1_F,\mathbf1_G\rangle|
 \le A N^{1-2/q}|F|^{1/q}|G|^{1/q}.
\]

Here A is the restricted-estimate constant; B below is the norm bound of
the genuine continuous l2 realization of this one kernel. They are not
names of the paper's two operators. Kernel positivity is used for the
complex block estimate, exactly as in checkpoint 18.

| Module | Named theorems | Checked content |
|---|---:|---|
| `DyadicRankMass.lean` | 12 | Rank intervals, coverage/disjointness, decreasing-sequence mass bound |
| `FiniteMagnitudeBlocks.lean` | 25 | Actual sorting, finite blocks, amplitudes, partition and coefficient mass |
| `FiniteBilinearImproving.lean` | 3 | Exact complex regrouping, coefficient norm bound, finite bilinear improving |

## Sorting the actual indices, including ties

Given a finite F and arbitrary f:Z->C, `decreasingMagnitudeList F f`
merge-sorts the actual indices of F by decreasing |f(x)|. Its permutation,
length, membership, absence of duplicate indices, and ordering properties
are proved. Equal magnitudes do not require distinct values or a strict
ordering. Every original index is retained, including those with f(x)=0.

Write the resulting list as x_0,...,x_(L-1), with L=|F|, and define

\[
 m_n=\begin{cases}|f(x_n)|,&n<L,\\0,&n\ge L.\end{cases}
\]

`rankMagnitude_nonneg`, `rankMagnitude_antitone`, and `rankMagnitude_tail`
prove that this is a nonnegative decreasing sequence with the stated zero
extension. In particular, no nonempty-support assumption is introduced.

## The finite rank partition

Put s_j=2^j-1 and I_j=[s_j,s_(j+1)) in the natural ranks. Then |I_j|=2^j.
The intervals are pairwise disjoint, and each rank n belongs to
I_(floor(log2(n+1))). For n<L, this block index is <=L.

The actual block `magnitudeBlock F f j` is the image under n->x_n of
the ranks in I_j with n<L. Only j=0,...,L are needed. The construction
uses a finite subset of Fin L, so no out-of-range list lookup occurs.

The proved consequences are:

- `magnitudeBlock_card_le`: |F_j|<=2^j;
- `magnitudeBlock_disjoint`: the actual finite sets are pairwise disjoint;
- `magnitudeBlock_cover`: their finite union is exactly F;
- `magnitudeBlock_sum`: summing any function over the blocks equals its
  sum over F, for every additive commutative monoid;
- `magnitudeBlock_norm_le`: |f(x)|<=m_(s_j) on F_j.

The amplitude is `magnitudeAmplitude F f j = m_(s_j)`. It is zero for
an empty block beyond the input length. A block containing zero-valued
indices also has the correct amplitude; the construction does not remove
such indices. The last nonempty block may have fewer than 2^j elements.

## The coefficient mass estimate

For every real p>0, set c_j=(2^j)^(1/p)*m_(s_j). The exact power identity
c_j^p=2^j*m_(s_j)^p is proved, including zero amplitudes.

For the next block, all ranks n in I_j precede s_(j+1). Monotonicity gives
m_(s_(j+1))^p<=m_n^p, and the full rank interval has 2^j elements. Thus

\[
 2^{j+1}m_{s_{j+1}}^p
 \le2\sum_{n\in I_j}m_n^p.
\]

This is `dyadic_rank_next_mass`. It holds even if part or all of the rank
interval is past L: the zero extension makes those terms zero.

Induction, using the exact finite interval-sum split, proves

\[
 \sum_{j=0}^{K}2^j m_{s_j}^p
 \le m_0^p+2\sum_{n<s_K}m_n^p.
\]

Every finite prefix sum of the zero-extended sequence is bounded by its
original mass. This includes the prefix of length one, so m_0^p is also
bounded by the original mass when L=0. Consequently

\[
 \sum_{j=0}^{K}c_j^p\le3\sum_{n<L}m_n^p
\]

for every finite K. `dyadic_rank_coefficient_mass` proves this generic
statement. `rankMagnitude_sum` identifies the ranked mass with the actual
sum over F by an injective, surjective finite reindexing. Specializing
K=L therefore gives the actual input theorem

\[
 \sum_{j=0}^{|F|}c_j^p\le3\sum_{x\in F}|f(x)|^p.
\]

This is `magnitudeBlock_coefficient_mass`. It has no assumed partition,
monotonicity or coefficient estimate: all of those have been constructed
and proved for the given F and f. Its p>0 range is stronger than the
p>=1 range needed for the corollary.

Using the exact norm of `finiteInputLp F f P`, the theorem
`magnitudeBlock_coefficient_lp_norm` proves

\[
 \Bigl(\sum_j |c_j|^p\Bigr)^{1/p}
 \le3^{1/p}\|f\mathbf1_F\|_p.
\]

P is an ENNReal exponent in Lean and p=P.toReal. All norms here are
Mathlib's genuine sequence-space norms. The proof covers the zero vector.

## Exact regrouping with complex phases

For any complex kernel K, define the actual finite pairing

\[
 B_{F,G}(f,g)=\sum_{x\in G}\sum_{y\in F}
 K(x-y)f(y)\overline{g(x)}.
\]

The rank partitions of F using f and G using g give

\[
 B_{F,G}(f,g)=\sum_i\sum_j B_{F_i,G_j}(f,g).
\]

`finiteKernelPairing_magnitudeBlocks` proves this identity by distributing
the finite convolution and applying the actual block-sum identities in
both variables. Complex conjugation is retained throughout. This algebraic
identity needs no positivity of K; positivity enters the bound below.

## The strong finite bilinear estimate

Put a=1/q-1/p and b=1/p-1/2. The previously checked actual block-family
estimate gives the right side below with the coefficient norms in place
of the original input norms. The new mass bounds supply one factor
3^(1/p) for each input. Thus `restricted_l2_finite_bilinear_improving`
proves, for every finite F,G and arbitrary complex f,g,

\[
 |B_{F,G}(f,g)|
 \le 3^{2/p}\left(
       \frac{A}{1-2^{-a}}+\frac{2^bB}{1-2^{-b}}
      \right)
      N^{1-2/p}\|f\mathbf1_F\|_p\|g\mathbf1_G\|_p.
\]

The formal theorem allows 1<=p<2 and 0<q<p whenever its stated global
restricted q estimate holds. The paper uses p0<q<p<2. N is any positive
real number. The prefactor depends on A,B,p,q and not on N, the sets,
their cardinalities, the coefficients, or a chosen partition.

The theorem's analytic inputs are exactly the global restricted estimate,
source kernel positivity and a genuine continuous l2 operator norm bound.
It does not assume block data, a desired coefficient inequality, norm
duality or strong interpolation. The earlier high-low theorem supplies
the restricted estimate in the intended application. No new deep analytic
theorem or mathematical axiom is used.

## Remaining operator-norm step

The finite bilinear theorem is now complete. Corollary 4.15 remains partial
until it is connected to the output lp' norm and both actual operators.

One proposed finite-output duality route is as follows; it is **not yet a
Lean proof**. Let p'=p/(p-1)>=2 and u be the output of the coarse actual
lp-to-lp' realization. On a finite output set G, use the test

\[
 g(x)=|u(x)|^{p'-2}u(x).
\]

Then the desired identities are

\[
 \sum_{x\in G}u(x)\overline{g(x)}
   =\sum_{x\in G}|u(x)|^{p'},\qquad
 \|g\mathbf1_G\|_p^p=\sum_{x\in G}|u(x)|^{p'}.
\]

These identities, including zero coordinates and the exponent relation
(p'-1)*p=p', still need formal proofs. The nonnegative p'-2 avoids a
negative power at zero; p=2 can also be handled by the existing endpoint.
Apply the finite bilinear estimate, split off the zero-sum case, and
derive the finite output norm bound. The existing lp finite-sum norm
criterion then gives the full output norm bound. Membership of u in lp'
is already supplied by `lpL2Lift`.

Finally invoke `lp_opNorm_bound_of_finiteInputs` for all lp inputs, choose
q between p0 and p before N, retain both original l2 constants, translate
1-2/p to 1/p'-1/p, and assemble the interior range with p=2. No assertion
that these final connections are complete is made in this checkpoint.

## Verification and finite experiments

All 67 modules and the root receive a fresh build with the artifact cache
disabled: 3464 jobs pass without warnings or errors. All 551 named project
theorems pass the complete transitive axiom audit, allowing only propext,
Classical.choice and Quot.sound. The source scan checks 69 Lean files.

`scripts/check_dyadic_rank_blocks.py` checks 56113 finite inputs, including
all 55987 input vectors of length <=6 over a six-value Gaussian integer
alphabet and 126 structured longer inputs. The largest tested length is
1024. It verifies coverage, disjointness, cardinality and magnitude bounds,
then 280565 coefficient mass inequalities at p=1/2,1,3/2,2,3. The alphabet
has square integer magnitudes, so all tested powers are exact integers.
Ties, zero inputs, empty blocks and incomplete final blocks are included.

Another 768 exact Gaussian integer checks verify complex bilinear
regrouping, allowing signed and complex kernels. All pass. These finite
experiments are independent checks; Lean proves the all-input statements.
They do not verify output norm duality, the full operator corollary, or
the later prime-square operator hypotheses.

Workspace maintenance had cleared temporary caches. The saved checkpoint
18 was recovered and all 206 archive entries were verified. The exact
Lean 4.34.1 release archive hash and pinned dependency revisions were
verified before rebuilding. No version upgrade or proof-kernel change was
made. The archived manuscript and accepted revision fragments are unchanged.
The count of completely proved unconditional numbered results remains nine;
Lemma 3.21 retains its earlier explicit PNT hypotheses independently.

# Corollary 4.15: global restricted improving and weak distribution bounds

Current checkpoint 20: the full abstract Corollary 4.15 is complete,
including strong interior interpolation and p=2. This document records an
earlier stage; see [Strong_Improving_Complete.md](Strong_Improving_Complete.md)
for the completed proof and current scope.


Checkpoint 16 proves equation 4.17 (`e:restrictedimproving`), including its
exact N scaling, from Theorem 4.1 and the stated extra l2 bounds. It also
proves the actual restricted weak distribution estimate and the strong p=2
case for the unique continuous linear l2 realizations.

**The strong estimate for p0<p<2 in Corollary 4.15 is still open.** The
interpolation step for general lp inputs is not a hypothesis or an axiom in
this project. This checkpoint does not mark the whole corollary complete.

## Source and exact statement

The source is `c:improvinggeneral`, Corollary 4.15, beginning near line 2431
of `sources/current/Draft5.tex`. Equation 4.17 is the restricted pairing
estimate inside its proof. Equation 4.16 (`e:lpimproving`) is the full strong
conclusion and remains only partially covered.

Put

\[
 p_0=\frac{2(s+r)}{2r+s},\qquad p'=\frac p{p-1}.
\]

For every p0<p<=2, `highLow_AB_restricted_improving` proves that one D>0,
quantified before N, both kernels, windows and F,G, satisfies

\[
 |\langle A_N1_F,1_G\rangle|+|\langle B_N1_F,1_G\rangle|
 \le D N^{1/p'-1/p}|F|^{1/p}|G|^{1/p}
\]

for every positive real N and all finite F,G in the integers. There is no
remaining cardinality-product or common-interval restriction. In particular,
the sum estimate gives the source's estimate for each operator separately.
Empty input and test sets are included.

The hypotheses are the completed Theorem 4.1's actual abstract operator
inputs and two genuine uniform continuous linear l2 realizations. Their
l2 constants may be different. This result does not establish the
prime-square operator hypotheses.

## Four new modules

| Module | Checked content |
|---|---|
| `RestrictedPowers.lean` | Critical/conjugate exponent algebra, exact density scaling, uniform removal of losses, zero density |
| `RestrictedL2.lean` | Actual continuous linear l2 inputs, uniqueness, strong p=2 case, l2 pairing bound and globalization |
| `RestrictedImproving.lean` | Equation 4.17 for both actual kernels and all finite sets |
| `RestrictedWeak.lean` | Finiteness of positive superlevel sets, weak gauge/cardinality bounds and both-kernel restricted weak theorem |

They add 33 named theorems. The completed Theorem 4.1 and its scalar
optimization are reused rather than assumed in a new conditional statement.

## Exact exponents and normalization

For s,r>0, the following identities and inequalities are proved:

\[
 1<p_0<2,\qquad
 \frac1{p_0}=1-\frac{s}{2(s+r)}=:\theta,
 \qquad
 \frac1{p'}=1-\frac1p.
\]

Thus p>p0 gives epsilon=theta-1/p>0. For p<=2,
`1/2<=1/p`. The definitions are `improvingCriticalExponent` and
`holderConjugate`. Positivity and nonvanishing needed in the divisions are
checked before using these formulas.

For N>0 and nonnegative real f,g, the exact scaling identity is

\[
 N\left(\frac{fg}{N^2}\right)^{1/p}
 =N^{1-2/p}f^{1/p}g^{1/p}
 =N^{1/p'-1/p}f^{1/p}g^{1/p}.
\]

This is proved for real powers, including f=0 or g=0. It is used to convert
the normalized density estimate into the literal N power in equation 4.17.
No unspecified comparison or hidden N-dependent constant is involved.

## Uniform removal of the endpoint losses

The B_N endpoint has factor `(Log delta)^tau`, with the exact tau from
Theorem 4.1. The A_N endpoint has Phi(cstar,kappa,delta). For any sigma<theta
with sigma>0, the new modules prove, with constants uniform on 0<=delta<=1,

\[
 \delta^\theta(\operatorname{Log}\delta)^\tau
 \le C\delta^\sigma,
 \qquad
 \delta^\theta\Phi_{cstar,\kappa}(\delta)
 \le C'\delta^\sigma.
\]

For positive delta these follow from the already proved uniform Phi
sub-power bound, with epsilon=theta-sigma. A fixed logarithmic power is
first absorbed into Phi(1,1/2,delta). At zero, positivity of theta and sigma
makes both density powers vanish. This zero case is proved separately;
there is no limiting substitution at log(0).

The A_N coefficient is chosen once as the printed leading coefficient plus
one. Theorem 4.1 allows that choice, and the final restricted estimate is
independent of density. Taking sigma=1/p gives
`highLow_AB_power_small` for |F||G|<=N^2. It retains actual operator inputs
through `HighLowEndpointInputs` and does not assume an endpoint deduction.

## The genuine l2 hypothesis

`KernelL2Bound K C` means there exists a continuous complex-linear map

\[
 T:\ell^2(\mathbb Z)\longrightarrow\ell^2(\mathbb Z)
\]

with operator norm at most C, whose value on every finite indicator agrees
pointwise with the actual convolution by K. This is the restriction of the
source's uniform l2 convolution bound needed here. The source operator
itself supplies the map.

`kernelL2_realization_unique` proves that two such maps agree on the whole
l2 space. Agreement on singleton indicators gives agreement on their complex
multiples; Mathlib's proved density of finite-support vectors and continuity
then give equality. Thus the realization is determined by the kernel.

`kernelL2_pair_strong_two` supplies both realizations and proves

\[
 \|T_Af\|_2+\|T_Bf\|_2\le(C_{2,A}+C_{2,B})\|f\|_2
 \quad(f\in\ell^2).
\]

Since p'=2 at p=2 and the N exponent is zero, this is the strong p=2 case.
The interior p0<p<2 still requires interpolation.

## Larger cardinality products

The actual l2 input and the proved indicator norm identities imply

\[
 |\langle T1_F,1_G\rangle|
 \le C_2\sqrt{|F|}\sqrt{|G|}.
\]

After division by N this is `C2*delta^(1/2)`. If |F||G|>N^2, then delta>1;
since p<=2, real-power monotonicity gives
`delta^(1/2)<=delta^(1/p)`. This proves the same normalized restricted
bound in the missing range. The small-range and l2 constants are added
before N,F,G are introduced.

The result is global in F,G. This provides an alternative first step for
the source's interpolation/localization proof; no finite-propagation or
interval partition theorem is needed for this restricted deduction.
The subsequent strong argument remains to be established.

## Actual superlevel sets and restricted weak type

For a nonnegative kernel K and a positive level lambda, let

\[
 E=\{x:\lambda<|T1_F(x)|\}.
\]

`kernelL2Bound_superlevel_finite` proves that E is finite: the l2 output has
summable squared norms, those squares tend to zero along the cofinite
filter, and only finitely many can exceed lambda squared.

Every output is real and nonnegative. The earlier exact positive pairing
identity therefore gives

\[
 \lambda |E|\le|\langle T1_F,1_E\rangle|
 \le S|F|^{1/p}|E|^{1/p},
 \qquad S=D N^{1/p'-1/p}.
\]

For nonempty E the proof divides by the strictly positive power
`|E|^(1/p)` and uses `1/p'+1/p=1`. The empty case is handled directly.
The result is

\[
 \lambda |E|^{1/p'}\le S|F|^{1/p},
 \qquad
 |E|\le\left(\frac{S|F|^{1/p}}\lambda\right)^{p'}.
\]

The Lean result constructs an actual finite set E, proves its membership
is equivalent to the displayed superlevel condition on the whole integer
line, and proves the weak gauge inequality. `weak_gauge_to_cardinality`
proves the cardinality conversion. `highLow_AB_restricted_weak` connects
this to both kernels and all the actual source norm assumptions.

The positivity of A_N is used in this distribution step, as supplied by
the original theorem. The global complex pairing estimate itself did not
need that additional positivity. These are indicator-input weak bounds;
they are not a strong estimate for general inputs.

## Verification and numerical scope

The project now has 58 modules and 457 named theorem declarations; the
source scan covers 60 Lean files. All modules and the root receive a fresh
build, with the artifact cache disabled. All named theorem declarations
receive the complete transitive axiom audit with whitelist propext,
Classical.choice and Quot.sound. See the current verification logs.

The new exact experiment checks 11250 normalization cases, including 882
zero-product cases and 9303 larger-density cases. It examines 98304 distinct
finite positive-kernel pairings at three conjugate exponents (294912
pairing/exponent checks), and 36864 superlevel inequalities. Empty
superlevels and strict-threshold boundary cases are included. All pass.

The finite families use six integer kernels, all input subsets of
{-2,-1,0,1,2}, all output subsets of {-4,...,4}, and positive half-integer
levels. The normalization exponents are p=4/3,3/2,2. Integer powers remove
all radicals, so the checks use only integers and exact fractions. These
finite checks do not verify the unbounded analytic operator hypotheses or
the missing strong interpolation theorem. General real-parameter
restricted implications are proved in Lean.

No new mathematical axiom, deep input or manuscript correction is used.
The explicit PNT hypotheses in Lemma 3.21 remain independent.

## Remaining obligation

The nine fully proved numbered results, including Theorem 4.1, remain
unchanged. Corollary 4.15 is partial: equation 4.17, the actual restricted
weak consequence and p=2 are proved; the strong interior range is open.

Checkpoint 17 connects finite complex inputs, genuine lp operator
realizations, uniqueness and density, and proves the finite Schur lemmas;
see `Strong_Interpolation_Foundations.md`. The strong interpolation estimate
with the correct N scaling still needs to be proved. Checkpoint 18 also
closes the actual geometric weight and complex block/family estimates;
see `Interpolation_Geometry.md`. The rank construction, mass bound,
finite-output duality and final strong assembly remain open. The local source search did
not find a named Marcinkiewicz/Riesz--Thorin/restricted-weak theorem in the
pinned Mathlib; that search is recorded in
`verification/interpolation-availability.json`. This is a search result,
not a proof that no suitable result exists under another name. A concrete
proposed construction is recorded in `blueprint/Strong_Interpolation_Plan.md`;
it distinguishes checked supporting steps from the remaining unproved
construction, with no Lean placeholders added.

Checkpoint 19 constructs the rank blocks, proves the mass bound and derives
the strong finite bilinear estimate. See `Rank_Blocks_and_Finite_Bilinear.md`.
Finite-output norm duality and final strong operator assembly remain open.

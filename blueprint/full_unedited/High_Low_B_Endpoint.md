# Theorem 4.1: the complete B_N endpoint deduction

Checkpoint 13, 22 October 2026.

The B_N conclusion, equation `e:endimprovbn` (4.9), is proved in Lean from
the theorem's local estimate and actual operator norm assumptions. This
includes the exact logarithmic exponent, dyadic selection, the truncated
parameter range, empty admissible ranges and empty input/test sets.

**Theorem 4.1 is still partially complete.** Its A_N conclusion, the sharp
coefficient in `e:cstar`, and the subsequent strong-type interpolation
corollary are not asserted by this checkpoint. The prime-square operator
estimates supplying the abstract hypotheses are also later obligations.

## Source and theorem correspondence

The frozen source is `sources/current/Draft5.tex`. Its saved reference map is
`verification/Draft5.aux`.

| Item | Stable label | Typeset number | PDF page |
|---|---|---|---:|
| Full abstract high--low theorem | `t:improvinggeneral` | 4.1 | 25 |
| Local crude input | `e:bnv` | 4.3 | 26 |
| Low operator norm input | `e:lobn1` | 4.4 | 26 |
| High operator norm input | `e:hibn1` | 4.5 | 26 |
| B_N endpoint conclusion | `e:endimprovbn` | 4.9 | 26 |
| Pairing/balancing estimate | `e:Bbalance` | 4.12 | 26 |

The preferred scale is the expression labeled `e:Jchoice`. The source's
logarithmic conventions are retained exactly:

\[
 \Log x=2+|\log x|,\qquad \Log\Log x=2+\log(2+|\log x|),
\]
\[
 \Phi_{c,\kappa}(x)=\exp\!\left(c\frac{(\Log x)^\kappa}{\Log\Log x}\right).
\]

These are `paperLog`, `paperLogLog` and `paperPhi`. The last definition is
recorded for the next stage; defining it is not a proof of the A_N estimate.
The definitions have harmless total extensions at x=0 in Lean. Empty-set
cases are proved separately, with endpoint value zero.

## Exact formal statement for the B_N clause

Fix s,r>0, β≥0, γ≥β and C>0. In the paper, s≥1-v and v<1 imply s>0.
Let N>0, let K be a complex-valued convolution kernel on the integers, and
let I_x be any finite local window. Write

\[
 (K*\mathbf1_F)(x)=\sum_{y\in F}K(x-y),\qquad
 \langle K*\mathbf1_F,\mathbf1_G\rangle
       =\sum_{x\in G}\sum_{y\in F}K(x-y).
\]

The formal definitions are `indicatorConvolution` and
`restrictedKernelPairing`. Lean also proves that these finite sums equal
the corresponding infinite sums with the actual indicator functions and
complex conjugation in the second factor.

Assume the local inequality

\[
 |(K*\mathbf1_F)(x)|\leq C N^{-v}
                  \|\mathbf1_F\mathbf1_{I_x}\|_1.
\]

For each admissible dyadic J=2^k with

\[
 2\leq J\leq N^{(1-v)/s}/10,
\]

assume operators Lo:ℓ¹→ℓ∞ and Hi:ℓ²→ℓ² satisfying the decomposition on
indicators and the genuine norm bounds

\[
 \|Lo f\|_\infty\leq C N^{-1}J^s(\log J)^\gamma\|f\|_1,
 \qquad
 \|Hi f\|_2\leq C J^{-r}(\log J)^\beta\|f\|_2.
\]

These are the actual normed spaces `lp` in Mathlib. The proof does not need
linearity of the pieces, so the formal input permits a wider class of maps.
The decomposition is required only on indicators, since that is all the
restricted endpoint uses. The source's full operator decomposition implies
these hypotheses directly.

Then a single D>0, depending only on the fixed parameters and C, works for
every such N, kernel, local-window family and finite F,G with |F||G|≤N²:

\[
 \frac{|\langle K*\mathbf1_F,\mathbf1_G\rangle|}{N}
 \leq D\,\delta^{\,1-s/(2(s+r))}
       (\Log\delta)^{\gamma+s(\beta-\gamma)/(s+r)},
 \qquad \delta=\frac{|F||G|}{N^2}.
\]

This is `highLow_B_endpoint`. The constant is quantified before N, K,
the window family and F,G, so the required uniformity is formal. Common
interval support of F,G and positivity of K are not needed for this B_N
deduction; the paper itself notes the extension to arbitrary finite sets
with the stated cardinality product. Those assumptions may have other uses
in the remaining theorem and its applications.

The local windows in the source are integer intervals about x. The proof
uses only their finite-set interpretation. The exact local indicator is
`finiteIndicatorLp (F ∩ I_x) 1`; its norm is proved to be |F∩I_x|.

## 1. Indicators, actual norms and Cauchy--Schwarz

`finiteIndicatorLp` constructs the indicator as an element of `lp` at any
exponent, using its finite support. For positive finite p, Lean proves

\[
 \|\mathbf1_F\|_p=|F|^{1/p}.
\]

In particular, the input norms are exactly |F| and √|F| at exponents one
and two. Restricting an indicator to I is proved to give the indicator of
F∩I. These identities are not left as informal conversions between counts
and norms.

For the high output h in genuine ℓ², Mathlib's finite-energy bound gives

\[
 \sum_{x\in G}|h(x)|^2\leq\|h\|_2^2.
\]

The checked finite Cauchy--Schwarz inequality then proves

\[
 \left|\sum_{x\in G}h(x)\right|\leq\sqrt{|G|}\,\|h\|_2.
\]

The low output is bounded using its actual ℓ∞ norm and summing over G.
Triangle inequality and the decomposition therefore yield

\[
 \frac{|\langle K*\mathbf1_F,\mathbf1_G\rangle|}{N}
 \leq C\left(\delta J^s(\log J)^\gamma
       +\delta^{1/2}J^{-r}(\log J)^\beta\right).
\]

Lean checks the factors of N through

\[
 \sqrt\delta=\frac{\sqrt{|F|}\sqrt{|G|}}{N},\qquad N>0.
\]

The scalar balancing inequality is derived from these norm inputs; it is
not an extra hypothesis in the final operator theorem.

## 2. The crude estimate, including empty parameter ranges

Apply the local assumption to F={0}. Since |F∩I_x|≤1, this gives

\[
 |K(z)|\leq C N^{-v}.
\]

Two finite sums and triangle inequality imply

\[
 \frac{|\langle K*\mathbf1_F,\mathbf1_G\rangle|}{N}
       \leq C\delta N^{1-v}.
\]

The real-power identity used to normalize this expression is checked for
every N>0. In particular, the proof does not request a decomposition at J=2
when the admissible range is empty.

## 3. Exact balance identities

Put

\[
 u=s+r,\quad L=\Log\delta,\quad
 \theta=1-\frac{s}{2u},\quad
 \tau=\gamma+\frac{s(\beta-\gamma)}u
       =\frac{r\gamma+s\beta}u,
\]
\[
 T=\delta^{-1/(2u)}L^{(\beta-\gamma)/u},
 \qquad E=\delta^\theta L^\tau.
\]

For 0<δ≤1, all bases of real powers are positive, L≥2, θ>0 and τ≥0.
Lean proves the exact identities

\[
 \delta T^sL^\gamma=E,
 \qquad \delta^{1/2}T^{-r}L^\beta=E.
\]

It also proves δ≤E and δT^s≤E. The first follows from θ≤1 and L^τ≥1;
the second follows from the first balance identity and L^γ≥1. None of
these steps invokes an unproved asymptotic or optimization result.

## 4. Dyadic rounding that preserves the cutoff

When T≥2, choose a dyadic J rounded down:

\[
 2\leq J\leq T<2J.
\]

Its existence is proved using the Archimedean power lemma. If T is within
the admissible range, J remains within that range. An upward rounding can
fail this requirement near the cutoff.

Set

\[
 A=1+\frac1{2(s+r)}.
\]

Because β≤γ and log L≥0,

\[
 \log T=-\frac{\log\delta}{2u}
              +\frac{\beta-\gamma}{u}\log L
       \leq\frac{L}{2u}\leq AL.
\]

Thus log J≤AL, J^s≤T^s and J^(-r)≤2^r T^(-r). As β,γ≥0, the two exact
balance identities give

\[
 \delta J^s(\log J)^\gamma
 +\delta^{1/2}J^{-r}(\log J)^\beta
       \leq(A^\gamma+2^rA^\beta)E.
\]

This is the entire interior case, with an explicit parameter-dependent
constant and the printed logarithmic exponent.

## 5. Every boundary and fallback case

Write M=N^((1-v)/s)/10 for the upper cutoff.

| Situation | Checked choice or estimate | Resulting coefficient multiplying C E |
|---|---|---:|
| T≥2 and T≤M | Dyadic J≤T<2J | A^γ+2^r A^β |
| T≥2 and M<T | Crude estimate | 10^s |
| T<2 and 2≤M | J=2 | 2^s+1 |
| T<2 and M<2 | Crude estimate; no admissible scale required | 20^s |

For the exceeded-cutoff case, raising
N^((1-v)/s)<10T to the positive power s gives

\[
 N^{1-v}\leq10^sT^s.
\]

Then the crude bound is at most C10^s δT^s≤C10^s E. The exponent cancellation
((1-v)/s)s=1-v is explicitly checked with s≠0.

For T<2 and admissible J=2, use log 2≤1 for the low term, δ≤E, and
2^(-r)≤T^(-r), (log 2)^β≤L^β for the high term. This yields C(2^s+1)E.
This argument also covers preferred scales T<1.

For an empty admissible range M<2, the same cutoff calculation gives
N^(1-v)≤20^s. The crude bound is at most C20^s δ≤C20^s E. All positive
scales N are covered; there is no unproved sufficiently-large-N exception.

One explicit final choice is therefore

\[
 D=C\left(A^\gamma+2^rA^\beta+10^s+2^s+1+20^s\right)>0.
\]

No optimal constant is claimed. If F or G is empty, the pairing and density
are zero. Since θ>0, the endpoint is zero and the conclusion follows
directly, before any use of a logarithm of a positive density.

## Lean files and trust boundary

| Module | Checked content |
|---|---|
| `HighLowNotation.lean` | Exact Log/LogLog/Phi definitions, positivity, dyadic rounding down |
| `HighLowBalance.lean` | Density/log exponents, exact preferred-scale identities, logarithm bound |
| `HighLowOptimization.lean` | Full scalar optimization with all four range cases and an explicit constant |
| `HighLowPairing.lean` | Actual finite convolution, finite complex pairings, genuine lp-two energy and Cauchy--Schwarz |
| `HighLowEndpoint.lean` | Normalizations, local-kernel crude bound, endpoint from indicator-output inputs |
| `HighLowOperators.lean` | Exact indicator norms, standard infinite-sum identities, operator norm bridge and `highLow_B_endpoint` |

The operator norm estimates are the hypotheses of the abstract theorem.
This checkpoint proves their implication, rather than asserting them for
the prime-square kernels. No own-paper result is replaced by an axiom.
There are no extra mathematical axioms or proof placeholders.

The previous eight completed numbered results remain unchanged. Lemma 3.21
still has its two explicit PNT-limit hypotheses. No PNT or Siegel--Walfisz
input enters the new B_N argument. This checkpoint does not increase the
count of completely proved numbered results, because Theorem 4.1 also has
the unproved A_N conclusion.

## Verification and exact finite checks

The fresh build checks all 46 project modules. The source audit scans 48 Lean
files and the transitive axiom audit covers 372 named project theorems,
including the 51 added here. The only permitted foundational axioms are
`propext`, `Classical.choice` and `Quot.sound`.

`scripts/check_high_low.py` records zero failures using integer arithmetic
and exact fractions:

| Check | Cases |
|---|---:|
| Complete scalar optimization, rational subfamily s=r=1, β=γ=0, δ=T^(-4) | 56,164 |
| Admissible dyadic scales examined | 122,193 |
| Empty admissible ranges | 7,979 |
| Preferred scales below two | 2,220 |
| Interior-balance cases | 14,667 |
| Exceeded-cutoff cases | 39,277 |
| Examples where upward rounding exceeds the cutoff | 4,071 |
| Actual complex finite-kernel pairings | 6,144 |
| Empty input/test-set pairings | 378 |

The kernel tests use six finite kernels with Gaussian-integer coefficients
and every pair of subsets of {-2,-1,0,1,2}. They check the decomposition,
global high-output square energy, low-output supremum bound, combined pairing
bound and crude kernel estimate. Noninterval and empty sets are included.
Irrational norm inequalities are tested by squaring with the required sign
case, without converting to floating point.

The scalar experiment is explicitly restricted to its rational subfamily;
it does not numerically certify general logarithmic exponents. Lean proves
the full real-parameter result and its unbounded quantifiers. These finite
checks supplement that proof and do not replace it.

## Remaining part of Theorem 4.1

The next target is the A_N conclusion with every fixed coefficient larger
than

\[
 \frac{c_1s}{2^\kappa(s+r)^{\kappa+1}}.
\]

It requires the actual low/high/error pairing bound, the two density/scale
ranges, dyadic Q selection, domination of logarithmic losses by the exact
Phi function, and a uniform epsilon formulation of the sharp coefficient.
The displayed first-order Q choice should be handled with explicit epsilon
margins; uniform comparability of its first two contributions must not be
silently assumed. The subsequent interpolation corollary also remains open.

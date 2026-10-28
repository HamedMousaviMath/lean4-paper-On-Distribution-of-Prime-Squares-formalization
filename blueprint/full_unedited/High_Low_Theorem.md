# Theorem 4.1: complete restricted endpoint deduction

Current checkpoint 20: the full abstract Corollary 4.15 is complete,
including strong interior interpolation and p=2. This document records an
earlier stage; see [Strong_Improving_Complete.md](Strong_Improving_Complete.md)
for the completed proof and current scope.


Checkpoint 15 completes both restricted endpoint conclusions of Theorem 4.1,
`t:improvinggeneral`, from its abstract operator norm hypotheses. The main
Lean declaration is `PrimeSquares.highLow_AB_endpoint` in
`PrimeSquares/HighLowTheorem.lean`.

The source conclusions are equation 4.9 (`e:endimprovbn`), equation 4.10
(`e:endimprovan`) and the coefficient in equation 4.11 (`e:cstar`). The
epsilon interpretation of the coefficient is included. Theorem 4.1 is now
counted as a complete numbered result. The prime-square estimates that supply
its abstract hypotheses and the following interpolation corollary remain open.

## Exact conclusion

Let delta=|F||G|/N^2. One DB>0 and one DA>0, chosen before N, both kernels,
local windows and F,G, satisfy

\[
 \frac{|\langle B_N1_F,1_G\rangle|}{N}
 \le D_B\delta^{1-\frac{s}{2(s+r)}}
 (\operatorname{Log}\delta)^{\gamma+\frac{s(\beta-\gamma)}{s+r}},
\]

and

\[
 \frac{|\langle A_N1_F,1_G\rangle|}{N}
 \le D_A\delta^{1-\frac{s}{2(s+r)}}\Phi_{cstar,\kappa}(\delta)
\]

for every fixed

\[
 cstar>\frac{c_1s}{2^\kappa(s+r)^{\kappa+1}}.
\]

The proof includes all positive real N and all finite F,G in the integers
with |F||G|<=N^2, including empty sets and sets outside a common interval.
It therefore includes the paper's positive integer scales and its concluding
arbitrary-finite-set extension. The exact definitions
`Log x=2+abs(log x)` and `LogLog x=2+log(Log x)` are retained.

The finite convolution sum is defined with the source orientation x-y, and
the pairing is formally identified with the ordinary infinite sum against
the conjugate indicator in `restrictedKernelPairing_as_tsum`. Finite sums
are not used as a substitute for a different pairing.

## Source hypotheses and Lean correspondence

`HighLowEndpointInputs` collects only the indicator restrictions of the
source assumptions. Its operator norm fields use genuine Mathlib lp spaces.

| Source | Lean field or declaration | Exact restriction used |
|---|---|---|
| Positive B_N convolution kernel | `nonnegative`, `NonnegativeKernel` | Every kernel value has imaginary part zero and nonnegative real part |
| Equation 4.2, `e:anbnsupbound` | `domination` | Norm of A_N applied to any finite indicator is at most `(log N)^a` times the real part of B_N applied to that indicator |
| Equation 4.3, `e:bnv` | `local_bound` | The stated local l1 norm on a finite window, for all finite indicators |
| `e:lobn1`, `e:hibn1` | `B_decomposition`, `OperatorHighLowBound` | Genuine l1-to-linfinity and l2-to-l2 maps at every admissible dyadic J |
| `e:decompan`--`e:errorgeneral` | `A_decomposition`, `OperatorOrliczBound` | Genuine l1-to-linfinity and two l2-to-l2 maps at every admissible dyadic Q |

The final theorem assumes v<1, 1-v<=s, r>0, 0<=beta<=gamma, a>=0,
c0,c1,c>0, 0<kappa<1, and the strict coefficient inequality. These include
the printed parameter ranges. The printed requirements v>=0 and alpha>0
can be omitted for this deduction. Only the positivity of B_N is used;
the A_N kernel may be complex. Linearity and convolution formulas for the
individual decomposition pieces are unnecessary once their actual norm
bounds and indicator decomposition identities are given. These are
relaxations of source hypotheses, with no additional hypothesis introduced.

The local windows are arbitrary finite sets in the formal theorem. The
source intervals give a particular choice. No claim is made that the
prime-square kernels satisfy these hypotheses merely because the abstract
implication has been proved.

## Separate three-piece constants and error input

The A_N predicate retains three separate real constants CLo, CHi, CErr:

\[
\begin{aligned}
 \|\mathrm{Low}f\|_\infty
 &\le C_{Lo}N^{-1}Q^s(\log Q)^\alpha\|f\|_1,\\
 \|\mathrm{High}f\|_2
 &\le C_{Hi}Q^{-r}
 \exp\left(c_1\frac{(\log Q)^\kappa}{\log\log Q}\right)\|f\|_2,\\
 \|Ef\|_2
 &\le C_{Err}Q^{-r}(\log Q)^M(1+\log N)^{-1}\|f\|_2.
\end{aligned}
\]

The exponent M and the norm constant CErr are distinct fixed parameters.
The source provides every A>0; the proof uses its permitted value A=1,
with the associated power M=C_1. Thus it requires a consequence of the source
error hypothesis. The bound at every positive A is not assumed as an
unproved analytic statement within this abstract theorem; it is a given
operator hypothesis of the source, restricted to one value.

To use the scalar bound, the proof forms

\[
 C_A=1+|C_{Lo}|+|C_{Hi}|+|C_{Err}|.
\]

It proves that this number is positive and majorizes the three constants.
Every multiplier multiplying a constant is checked to be nonnegative before
it is enlarged. All constants and the power M are fixed before N and Q.
The notation C_A here denotes this auxiliary common constant; it is not an
identification of the source's error exponent with a norm constant.

## Actual operator-to-pairing bridge

`finiteIndicatorLp` is a genuine element of lp, with checked identities

\[
 \|1_F\|_1=|F|,\qquad\|1_F\|_2=\sqrt{|F|}.
\]

The three output functions for an indicator are a bounded low function and
two actual l2 functions. Triangle inequality and the proved finite l2
Cauchy--Schwarz estimate give

\[
 |\langle A_N1_F,1_G\rangle|
 \le |G|\|\mathrm{Low}1_F\|_\infty
 +(\|\mathrm{High}1_F\|_2+\|E1_F\|_2)\sqrt{|G|}.
\]

The input norm identities and exact normalization by N then yield

\[
\begin{aligned}
 \frac{|\langle A_N1_F,1_G\rangle|}{N}
 \le C_A\bigg[&\delta Q^s(\log Q)^\alpha
 +\delta^{1/2}Q^{-r}
  \exp\left(c_1\frac{(\log Q)^\kappa}{\log\log Q}\right)\\
 &+\delta^{1/2}Q^{-r}(\log Q)^M(1+\log N)^{-1}\bigg].
\end{aligned}
\]

This is `restrictedKernelPairing_orlicz_bound`, deduced from actual output
norms. The final theorem does not take this paper-specific scalar pairing
bound as a hypothesis.

## Positive-kernel pairing domination

For a nonnegative B_N kernel, every B_N indicator output is real and
nonnegative. Consequently its finite pairing equals the sum of those
nonnegative real outputs, and its norm equals that same sum. This identity
is proved in `restrictedKernelPairing_norm_positive`.

Summing the source pointwise domination and using triangle inequality gives

\[
 |\langle A_N1_F,1_G\rangle|
 \le(\log N)^a|\langle B_N1_F,1_G\rangle|.
\]

The normalized identity is `restrictedKernelPairing_domination_normalized`.
It accounts explicitly for the positivity needed to pass from pointwise
domination to a norm of the B_N pairing. The completed B_N endpoint from
checkpoint 13 is then applicable.

## Uniform scalar optimization: every density range

Set u=s+r, k=1/(2u), L=Log(delta) and
W(L)=L^kappa/(2+log L). Checkpoint 14 proved the actual dyadic balancing
bound with every coefficient above the printed leading one. The full
scalar implication, including the remaining ranges, is now
`orlicz_scalar_endpoint`.

The proof chooses

\[
 d=\frac{c_0}{k+1+\log4}>0.
\]

It proves d<=c0/(k+1). It also proves the following useful implication:
if L>=2 and L<=d*t, then log4<=c0*t. This is an elementary multiplication
by a positive denominator, checked in `orlicz_small_cutoff`.

There are three cases:

1. **Complementary range:** d*(log N)^c<=L. Positive domination and the
   B_N endpoint bound the A_N pairing by a fixed constant times
   `(log N)^a*delta^theta*L^tau`. The already proved uniform logarithmic
   absorption `log_density_domination_le_orlicz` bounds this by
   `D*delta^theta*Phi(cstar,kappa,delta)` over the entire density interval.
2. **Large L in the other range:** L>T, or L>=T at the chosen threshold,
   and L<=d*(log N)^c. The earlier constructed dyadic scale is admissible
   since d<=c0/(k+1), and its three scalar contributions have the required
   bound. The actual error decay factor is included.
3. **Bounded L in the other range:** L<T and L<=d*(log N)^c. The special
   choice of d proves that the fixed dyadic Q=4 is admissible. For
   theta=1-s/(2u)<=1 the proof checks
   `delta<=delta^theta` and
   `sqrt(delta)<=exp(T)*delta^theta`. These follow from 0<delta<=1 and
   L<=T. Substitution at Q=4 gives a fixed multiple of delta^theta;
   Phi>=1 completes the estimate.

An empty admissible Q range is covered by the first case: either remaining
case entails an admissible Q, as proved. No decomposition at an inadmissible
scale is invoked. The low/high/error terms include their separate constants
through C_A, and their common endpoint constant is selected before N,delta.

One valid unoptimized scalar constant is

\[
 D_A=D_BD_C+3C_A+C_A C_{\rm compact},
\]

where D_C is the uniform complementary-range absorption constant and
C_compact is the explicitly defined fixed-Q coefficient in
`orliczCompactConstant`. The density threshold T depends only on the fixed
parameters, alpha and M. Its dependence is permitted and never involves N,
F or G.

The sharp asymptotic step uses the strict-margin scale
`log Q approximately kL+bW(L)`, with
`c1*k^kappa/(s+r)<b<cstar/s`. It proves the literal log(log Q) scaling and
rounding limits. The particular first-order expansion in `e:Qchoice` is
not formalized; the epsilon-margin construction proves the same endpoint
conclusion directly. See `blueprint/Orlicz_A_Scalar_Balance.md` for that step.

## Small scales, zero density and uniformity

The operator bridge's growth and error-decay inequalities use N>=1. For
nonempty F and G, their cardinalities are positive integers and
`1<=|F||G|<=N^2`. If N>0, this implies N>=1. This deduction is proved in the
final theorem. Thus every smaller positive N already has an empty F or G.

If either set is empty, the actual pairing vanishes. Since
`theta=1-s/(2(s+r))>0`, the density factor at zero vanishes too. These cases
are handled before applying any positive-density scalar result. In
particular, no logarithm at a zero density is used in a limit argument.
The total Lean extensions of Log and Phi cause no ambiguity in the zero
endpoint.

## Verification and numerical scope

Checkpoint 15 adds four modules and 18 named theorems. The whole project has
54 modules and 424 named theorem declarations. Every module and the root
receive a fresh build with the artifact cache disabled, passing 3451 jobs.
The complete source scan covers 56 Lean files. Every named theorem receives
a transitive axiom audit with exactly the whitelist propext,
Classical.choice and Quot.sound. See the current verification logs.

The new independent exact finite experiment checks 6144 actual complex
convolution pairings, including 378 empty pairs, the three-piece norm bound,
positive-kernel identities, 18432 domination cases, 110592 normalized
domination cases, and 13104 normalization identities with separate constants.
Square-root sums are certified by integer isolating intervals with exact
equality detection; no floating-point arithmetic is used. The report and
reproducible script are `verification/three-piece-pairing-numerical.json`
and `scripts/check_three_piece_pairing.py`.

These numerical checks concern finite pairing components. They do not test
the unbounded analytic optimization, all-scale operator hypotheses or the
sharp coefficient; those implications are established by Lean. No external
analytic input, PNT or new mathematical axiom is used in Theorem 4.1.

## Status and next dependency

The nine unconditional completed numbered results are 3.1, 3.11, 3.12,
accepted revised 3.14, accepted revised Corollary 3.16, and original 3.20,
3.24, 3.27 and Theorem 4.1. Lemma 3.21 keeps its explicit two PNT-limit
hypotheses. The full archived sources and accepted revision fragments are
unchanged. No new manuscript statement correction is required by this proof.

Next is Corollary 4.15 (`c:improvinggeneral`): deduce the strong lp-improving
bound from the restricted endpoints and uniform l2 bounds. That interpolation
argument remains an open obligation; no strong lp or prime-square main theorem
is claimed here.

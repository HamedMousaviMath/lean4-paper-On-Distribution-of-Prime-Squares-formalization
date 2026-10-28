# Theorem 4.1: Orlicz growth and sharp A_N scalar balance

Checkpoint 14 continues the B_N endpoint proved in checkpoint 13. It proves
four new modules, containing 34 named theorems, for the A_N proof. Theorem
4.1 remains partial: its uniform A_N conclusion from actual operator norm
hypotheses has not yet been assembled.

## Source and exact scope

The source is `sources/current/Draft5.tex`, Theorem 4.1,
`t:improvinggeneral`, with `e:Abalance`, `e:endimprovan`, `e:cstar`,
`e:Lognotation` and `e:defPhi`. The archived TeX/PDF are unchanged.

The new modules are:

| Module | Checked content |
|---|---|
| `OrliczGrowth.lean` | Exact Phi identities, three limits, bounded-error control, uniform logarithmic absorption and uniform sub-power bounds |
| `OrliczBalance.lean` | Literal high-weight scaling, sharp leading coefficient, strict balancing margins, actual dyadic choice and all three exponent limits |
| `OrliczScalar.lean` | Exact normalization of low/high terms and a bound for the actual three-term scalar sum at that dyadic choice |
| `OrliczCutoff.lean` | Complementary density-range absorption, admissibility of the selected Q and the actual error decay factor |

No endpoint estimate for A_N, scalar optimization theorem, analytic
asymptotic or prime distribution theorem is assumed. Each limiting and
inequality statement is proved from the pinned Mathlib. The functions q used
in intermediate scaling lemmas are general real functions; the final scalar
lemmas construct an actual dyadic Q. The final `exists_admissible_dyadic_orlicz_bound`
does not take a desired asymptotic of Q as a hypothesis.

## Exact logarithmic conventions

Write

\[
 L=\operatorname{Log}\delta=2+|\log\delta|,\qquad
 W_\kappa(L)=\frac{L^\kappa}{2+\log L}.
\]

The definition `orliczWeight` is exactly W. The checked identity is

\[
 \Phi_{c,\kappa}(\delta)=\exp\bigl(cW_\kappa(\operatorname{Log}\delta)\bigr).
\]

For 0<delta<=1, L=2-log(delta), and delta=exp(2-L). The identity
`paperLog_exp_two_sub` is proved for every L>=2. The additive twos in the
paper's definitions are retained throughout.

For kappa>0 the module proves

\[
 \frac{\log L}{W_\kappa(L)}\to0,\qquad
 \frac1{W_\kappa(L)}\to0.
\]

For kappa<1 it proves W_kappa(L)/L -> 0. For the first limit, the exact
quotient is `(2 log L + (log L)^2)/L^kappa`. Both terms tend to zero by
Mathlib's proved logarithm-versus-power limits. The inverse-weight limit
uses `(2+log L)/L^kappa`. The sublinear-weight limit factors as
`L^(kappa-1)/(2+log L)`.

These limits yield actual uniform estimates, including their bounded range:

- For every kappa>0, c>0 and real m, there is D>0 such that
  `(Log x)^m <= D*Phi(c,kappa,x)` for every x. In particular this holds
  for every positive density.
- For 0<=kappa<1, c>=0 and epsilon>0, there is D>0 such that
  `Phi(c,kappa,delta) <= D*delta^(-epsilon)` simultaneously for
  0<delta<=1.
- Consequently `delta^theta*Phi(c,kappa,delta)` is bounded by
  `D*delta^(theta-epsilon)` on that same interval, for arbitrary real theta.

Constants are quantified before delta. The bounded-range argument selects a
fixed threshold U>=2 and uses elementary real-power inequalities below U.
Thus these are not only statements about an unspecified sufficiently small
density. The last estimate is useful for the later interpolation argument;
that corollary itself is still open.

## Literal high denominator

The high term in `e:highgeneral` uses `(log Q)^kappa/log(log Q)`.
Put q=log Q. For any function q(L) with q(L)/L -> k>0, the proof establishes

\[
 \frac{\log q(L)}{\log L}\to1,\qquad
 \frac{q(L)^\kappa/\log q(L)}{W_\kappa(L)}\to k^\kappa.
\]

The logarithmic ratio follows by taking the logarithm of q(L)/L, whose
limit is log(k), and dividing by log L -> infinity. For the second ratio,
the exact algebra is

\[
 \frac{q(L)^\kappa/\log q(L)}{L^\kappa/(2+\log L)}
 =\left(\frac{q(L)}L\right)^\kappa
   \frac{1+2/\log L}{\log q(L)/\log L}.
\]

All needed positivity and nonvanishing conditions hold eventually and are
checked in Lean. The literal denominator and the paper's LogLog denominator
are connected by this proved limit, with no informal replacement of one by
the other.

## Sharp coefficient and actual dyadic scale

Let u=s+r, k=1/(2u), where s,r>0. Define

\[
 c_{\rm lead}=\frac{c_1s}{2^\kappa u^{\kappa+1}}
 =s\frac{c_1k^\kappa}{u}.
\]

`orliczLeadingCoefficient_eq` proves this equality with real powers. Given
cstar>c_lead and c1>0, the proof chooses b satisfying

\[
 \frac{c_1k^\kappa}u<b<\frac{cstar}s.
\]

In particular b>0 and

\[
 sb<cstar,\qquad c_1k^\kappa-rb<sb<cstar,\qquad -rb<cstar.
\]

The candidate logarithm is y(L)=kL+bW_kappa(L). Since W/L -> 0, y/L -> k,
so y -> infinity. An actual dyadic Q=2^n is chosen by rounding exp(y) down:

\[
 Q\le e^{y(L)}<2Q.
\]

For all L the chosen Q is at least two. The two-sided rounding bounds hold
for sufficiently large L. They give
`abs(log Q-y(L)) <= log 2`. The inverse-weight limit proves

\[
 \frac{\log Q-kL}{W_\kappa(L)}\to b.
\]

The index function n(L) is fixed before the low logarithmic power alpha,
the error power M, the error decay exponent A and N. Its existence is proved
using the earlier dyadic rounding lemma; it is not an extra hypothesis.

## The three actual scalar terms

Set delta=exp(2-L), q=log Q and theta=1-s/(2u). After division by delta^theta,
the low, high and error terms are exponentials with respective exponents

\[
\begin{aligned}
 E_{\rm low}&=s(q-kL)+\alpha\log q+2sk,\\
 E_{\rm high}&=-r(q-kL)+c_1q^\kappa/\log q-2rk,\\
 E_{\rm err}&=-r(q-kL)+M\log q-2rk.
\end{aligned}
\]

The equalities for this normalization are proved in
`orlicz_low_term_exact` and `orlicz_high_term_exact`; the constants from the
additive two in L are included. The three exponent ratios tend to

\[
 E_{\rm low}/W\to sb,\quad
 E_{\rm high}/W\to c_1k^\kappa-rb,\quad
 E_{\rm err}/W\to-rb.
\]

The polynomial logarithms vanish in these ratios by the proved limits.
The strict margins therefore give, for all sufficiently large L,

\[
\begin{aligned}
 &\delta Q^s(\log Q)^\alpha
 +\delta^{1/2}Q^{-r}
   \exp\left(c_1\frac{(\log Q)^\kappa}{\log\log Q}\right)
 +\delta^{1/2}Q^{-r}(\log Q)^M\\
 &\hspace{2cm}\le3\delta^\theta\Phi_{cstar,\kappa}(\delta).
\end{aligned}
\]

This is `exists_dyadic_orlicz_scalar_bound`. It is an inequality for the
actual terms, beyond a limit calculation of their logarithms. The density
threshold may depend on alpha and M, as allowed for fixed theorem parameters.
The proof uses strict margins for the epsilon formulation of the conclusion.
It does not need bounded-factor comparability of the low and high terms at
the paper's first-order displayed choice.

## Cutoff and error decay

The dyadic choice satisfies log Q<=y(L), while y(L)/L -> k. Consequently
log Q <= (k+1)L eventually. If

\[
 L\le \frac{c_0}{k+1}(\log N)^c,
\]

the source cutoff log Q <= c0*(log N)^c follows. This is checked for the
same Q as in the scalar inequality.

For N>=1 and A>=0, `error_decay_factor_le_one` proves
`(1+log N)^(-A) <= 1`. All other factors of the error term are nonnegative,
so multiplying by this decay factor preserves the scalar upper bound.
`exists_admissible_dyadic_orlicz_bound` combines the cutoff, the actual dyadic
choice and the three-term bound with this decay factor. It works uniformly
in N and A once the sufficiently-large-L condition holds. The source's
separate constants implicit in the operator bounds and C_A must still be
carried through the operator bridge; they are not certified as equal to one.

## Complementary density range

For any d>0, a>=0, c>0 and x>=0, the elementary cutoff implication is proved:

\[
 dx^c\le L\quad\Longrightarrow\quad
 x^a\le d^{-a/c}L^{a/c}.
\]

It follows that for any real theta,tau and cstar,kappa>0, one D>0 works for
all N>=1 and 0<delta<=1 satisfying `d*(log N)^c <= Log delta`:

\[
 (\log N)^a\delta^\theta(\operatorname{Log}\delta)^\tau
 \le D\delta^\theta\Phi_{cstar,\kappa}(\delta).
\]

This is `log_density_domination_le_orlicz`. Applied to the already proved
B_N exponent tau, it is the scalar absorption required in the complementary
range of the source proof. The positive-operator domination and finite
pairing bridge needed for that application remain to be connected.

## What remains before marking Theorem 4.1 complete

1. Deduce the actual three-piece A_N pairing inequality from its genuine
   l1-to-linfinity and l2-to-l2 operator hypotheses, retaining the fixed
   operator constants and the chosen C_A. Use the existing indicator/lp
   infrastructure from the B_N proof.
2. Connect positive B_N kernels and the stated A_N domination to a pairing
   domination; use the B_N theorem and the complementary-range scalar bound.
3. Handle the bounded-density range uniformly, including bounded N and an
   empty admissible Q range. A fixed Q=2 or 4 may only be used after proving
   it is admissible. State the discrete N domain explicitly; the new cutoff
   and error-decay results assume N>=1.
4. Include empty input/test sets and combine all ranges with one constant
   quantified before N,F,G. Only then mark `e:endimprovan` and the full
   theorem complete. The following interpolation corollary and the
   prime-square operator norm estimates are later obligations.

No new source correction has been established in this checkpoint. No
unproved own-paper lemma has been classified as a deep external input.
The existing explicit PNT hypotheses in Lemma 3.21 remain separate and are
not used anywhere in these four modules.

## Verification

The checkpoint contains 50 project modules and 406 named project theorems.
All 50 modules receive a fresh local build with the artifact cache disabled;
all 406 named theorem declarations receive the complete transitive axiom
audit. The whitelist is exactly propext, Classical.choice and Quot.sound.
The source scan covers 52 Lean files. See the accompanying current logs.

No new numerical experiment is claimed for these unbounded real-parameter
analytic estimates. Their verification is the Lean proof. Earlier finite
experiments are preserved with their original scopes, including the B_N
rational scalar and Gaussian-integer convolution checks; those experiments
do not validate the new A_N asymptotics. The ZIP manifest is checked against
every archived entry, and the frozen paper sources keep their recorded hashes.

# Corollary 4.15: complete strong improving deduction

The source is `c:improvinggeneral`, equation 4.16 (`e:lpimproving`), near
line 2431 of the archived `sources/current/Draft5.tex`. All 70 modules and the root received a fresh build: 3467 jobs pass
without warnings or errors. All 565 named theorems pass the transitive
axiom audit; 72 Lean files pass the source scan.

The paper's abstract high-low assumptions, positivity of both kernels and
two genuine uniform l2 bounds imply the full strong improving conclusion:

\[
 \|A_N f\|_{p'}+\|B_N f\|_{p'}
 \le D_p N^{1/p'-1/p}\|f\|_p,
 \qquad \frac{2(s+r)}{2r+s}<p\le2.
\]

The constant is chosen before N, the kernels, the windows and the input.
The formal statement works for every positive real N. Both operators are
actual Mathlib continuous complex-linear maps between sequence spaces,
and they agree with the actual convolution on every finite complex input.
The prime-square operators' high-low hypotheses are not established here.

## Exact statement and new declarations

`PrimeSquares.highLow_AB_strong_improving` is the paper-facing theorem.
It uses P,Q:ENNReal with P.toReal=p and Q.toReal=p/(p-1), and the ordinary
Fact instances 1<=P and 1<=Q needed for Banach sequence spaces.
`improving_exponents_exist` constructs these parameters for every real
1<p<=2: P=ofReal(p), Q=ofReal(p/(p-1)), with both finite and P<=2<=Q.
Thus this parameterization does not restrict the source's real exponent range.

| Module | New named theorems | Role |
|---|---:|---|
| `FiniteOutputDuality.lean` | 8 | Conjugate algebra, complex test identities, cancellation and genuine output norm |
| `StrongImproving.lean` | 4 | Actual finite convolution agreement, strong operator norm and combining two maps |
| `StrongImprovingTheorem.lean` | 2 | Real exponent parameters and full abstract Corollary 4.15 |

No interpolation conclusion, duality assertion or desired strong norm is
an external assumption. These are deductions from the already proved
finite bilinear estimate and the source's genuine operator hypotheses.

## Finite-output duality, including zero coordinates

Let 1<p<=2 and put R=p/(p-1). Then R>=2,
(R-1)p=R and 1/R=1-1/p. Given a complex sequence u, define

\[
 g(x)=|u(x)|^{R-2}u(x).
\]

The test has the same complex phase as u. The pairing conjugates the
test. At a nonzero coordinate, ordinary positive-base real-power laws give

\[
 u(x)\overline{g(x)}=|u(x)|^R,
 \qquad |g(x)|^p=|u(x)|^{(R-1)p}=|u(x)|^R.
\]

At a zero coordinate, g(x)=0. This includes R=2, where the real-power
convention gives 0^0=1 but its product with u(x)=0 is still zero. Both
identities therefore remain valid. The formal proofs split off this case
before using positive-base power addition. They retain the complex
conjugation and prove the pairing identity as a complex equality.

For a finite output set G let S=sum_(x in G)|u(x)|^R>=0. The identities yield

\[
 \sum_{x\in G}u(x)\overline{g(x)}=S,
 \qquad \|g\mathbf1_G\|_p=S^{1/p}.
\]

Suppose every finite output test satisfies

\[
 \left|\sum_{x\in G}u(x)\overline{h(x)}\right|
 \le M\|h\mathbf1_G\|_p,\qquad M\ge0.
\]

Testing with g gives S<=M*S^(1/p). If S=0, then S<=M^R immediately.
If S>0, divide by its positive 1/p power to get
S^(1/R)<=M, then raise to the positive power R. Thus S<=M^R for every
finite G, including the empty set. `duality_power_cancel` checks precisely
this division, zero case and real-power argument.

`finite_output_power_bound` proves the finite-sum bound, and
`lp_norm_le_of_finite_pairing` invokes Mathlib's finite-sum norm criterion
to obtain ||u||R<=M for an actual u in lp(R). The proof does not require
the untruncated g to belong to lp(p); only its finite truncation is used.
No representation theorem for the Banach dual is assumed or needed.

## The sharp norm on the actual operator

Fix one positive kernel K, 0<q<p<2, N>0, and constants A,B>=0. Assume

\[
 |\langle K*\mathbf1_F,\mathbf1_G\rangle|
 \le A N^{1-2/q}|F|^{1/q}|G|^{1/q}
\]

for all finite sets, and an actual continuous l2 realization with norm
at most B. Set

\[
 a=1/q-1/p>0,\qquad b=1/p-1/2>0,
\]
\[
 C(A,B,p,q)=3^{2/p}\left(
 \frac{A}{1-2^{-a}}+\frac{2^b B}{1-2^{-b}}\right).
\]

The already checked theorem `restricted_l2_finite_bilinear_improving`
proves, for arbitrary finite F,G and complex f,h,

\[
 |B_{F,G}(f,h)|\le C(A,B,p,q)N^{1-2/p}
       \|f\mathbf1_F\|_p\|h\mathbf1_G\|_p.
\]

The existing contractive inclusions lp(p)->lp(2)->lp(R), composed with
the l2 realization, give a coarse actual continuous map U:lp(p)->lp(R).
This supplies output membership. Its finite-input coordinate identity
identifies U(f*1_F) with K*(f*1_F). Applying finite-output duality with

\[
 M=C(A,B,p,q)N^{1-2/p}\|f\mathbf1_F\|_p\ge0
\]

gives the sharper norm bound for every finite input. The previously proved
`lp_opNorm_bound_of_finiteInputs` extends it by density with the same
constant. This proves `restricted_l2_strong_improving`; its conclusion is
a genuine `KernelLpBound`, not a scalar model or a finite-support estimate.

The generic lemmas `kernelLp_realization_single` and
`kernelLp_realization_finiteInput` prove that every such realization agrees
with finite convolution for arbitrary complex coefficients. Agreement on
indicators is sufficient by linearity. The existing uniqueness theorem
identifies any two continuous realizations with that agreement.

## Both source operators and all exponent cases

Write p0=2(s+r)/(2r+s). The source parameters imply 1<p0<2. For
p0<p<2 choose q=(p0+p)/2 before N. The already proved global restricted
equation 4.17 supplies one constant A>0 uniform in N and both kernels.
Each individual restricted pairing is bounded by their sum.

Apply the strong one-kernel theorem separately, keeping the source's two
l2 constants B_A and B_B. Positivity of A_N is an explicit source
hypothesis at line 2300; positivity of B_N is already included in
`HighLowEndpointInputs`. It is not a new mathematical restriction.

Let C_A=C(A,B_A,p,q) and C_B=C(A,B_B,p,q). Both are nonnegative and
independent of N. The checked assembly chooses D=C_A+C_B+1>0 and proves
the sum of the two norms is bounded by D*N^(1-2/p)*||f||p for every f.
The harmless added one ensures strict positivity even for zero operators.
The checked conjugate identity rewrites the exponent as 1/p'-1/p.

For p=2 the coarse realizations already have the genuine l2 bounds;
N^(1-2/p)=1. The assembly uses D=B_A+B_B+1 and requires no limiting
interpolation argument. The final theorem gives the two actual maps,
their finite convolution identities, and the norm estimate for every
actual lp input. Uniformity is expressed by the quantifier order.

The proof establishes the global estimate directly from global equation
4.17, so the paper's last partition into intervals is unnecessary in
this formal proof. This is an alternative proof of the same conclusion.

## Verification and exact experiments

All 70 project modules and the root were freshly compiled with the
artifact cache disabled. The 3467-job build has no warnings or errors.
Every one of the 565 named project theorems passes the transitive audit,
allowing only propext, Classical.choice and Quot.sound. The source scan
checks 72 Lean files and finds no placeholders or additional axioms.
Exact theorem/audit coverage and fresh module/import coverage are checked.
No Lean source changed after these checks.

`scripts/check_finite_output_duality.py` independently checks 223988 finite
identity instances: 55987 exhaustive vectors of length <=6 over a six-value
Gaussian integer alphabet and 10 structured vectors through length 1024,
at output exponents 2,4,6,8 and input exponents 2,4/3,6/5,8/7. All pass.
Every operation is integral, including independently checked perfect roots;
there is no floating point. Empty, zero and nonreal inputs are included.

The diagnostic u=(1,i) at output exponent four gives pairing 2 with the
correct test and 0 with a mistakenly conjugated phase. The test suite
therefore detects this particular phase error. The experiment covers
sampled exponents only. Lean proves the full real exponent statements;
the experiment does not independently verify the operator estimate or
the prime-square high-low inputs. Exact ranges, digest and arithmetic
are recorded in `verification/finite-output-duality-numerical.json`.

No new deep input is used in Corollary 4.15. The two earlier explicit PNT
limits for Lemma 3.21 are unchanged and are not used here. The archived
manuscript and accepted revision fragments are unchanged. The next work
is to establish the prime-square operators' inputs and connect the main
applications, with every genuinely external analytic assumption explicit.

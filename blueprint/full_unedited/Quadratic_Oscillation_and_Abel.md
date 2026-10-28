# Quadratic oscillation and actual progression Abel summation

Checkpoint 24. This is the exact partial-summation identity used in the
proof of Lemma 6.5. It does not yet estimate the resulting error terms or
assert a progression prime-number theorem.

## The actual phase and its derivative

For real theta and real t define

\[
 g_\theta(t)=\exp(-2\pi i\theta t^2).
\]

`quadraticOscillation` uses the real coefficient -2*pi*theta*t^2,
coerced to C and multiplied by i before exponentiation. It has exactly
the paper's negative phase. At every natural n it is proved equal to
`negativeFourierCharacter ((n:Z)^2) (theta:PrimeCircle)`.

The offset theta is a real number here. No periodicity in theta is claimed
for arbitrary noninteger t; the oscillatory integral uses the chosen real
major-arc offset. The integer-indexed Fourier character agreement is
proved separately.

Ordinary real differentiation, then complex coercion and the complex
exponential chain rule, prove

\[
 g'_\theta(t)=-4\pi i\theta t\,g_\theta(t).
\]

This is an actual `HasDerivAt` statement for every real theta,t.
`quadraticOscillation_deriv` identifies the bundled derivative function.
Both the phase and its derivative are continuous, so they are integrable
on every compact real interval. No differentiability or integrability
hypothesis is passed to the final Abel theorem.

The actual complex exponential has unit norm. Consequently

\[
 |g_\theta(t)|=1,\qquad |g'_\theta(t)|=4\pi|\theta||t|.
\]

For 0<=t<=N this yields the explicit uniform derivative bound
4*pi*abs(theta)*N. These are unbounded Lean proofs, not numerical samples.

## Actual progression coefficients and prefixes

For a natural modulus q, a residue r in ZMod q and n natural, define

\[
 c_{q,r}(n)=\begin{cases}\Lambda(n),&n\equiv r\pmod q,\\0,&\text{otherwise},\end{cases}
 \qquad
 C_{q,r}(x)=\sum_{0\leq n\leq\lfloor x\rfloor}c_{q,r}(n).
\]

Both are complex-valued in Lean. They are actual sums of Mathlib's von
Mangoldt function; all prime powers remain. Since Lambda(0)=0, the
coefficient at zero and the prefix at zero are proved to vanish.

`squareResidueSum_as_coeff` proves the exact identification

\[
 W_r(\theta)=\sum_{n\in S}g_\theta(n)c_{q,r}(n),
\]

where W_r is the earlier unnormalized residue sum. This connects the
actual residue filter to the coefficients used by Mathlib's Abel formula,
including the phase and the order of complex multiplication.

## The actual Abel formula

Let 0<=a<=b be reals. Applying the pinned Mathlib theorem
`sum_mul_eq_sub_sub_integral_mul` to these actual coefficients and the
proved differentiable phase gives

\[
 \sum_{\lfloor a\rfloor<n\leq\lfloor b\rfloor}
     g_\theta(n)c_{q,r}(n)
 =g_\theta(b)C_{q,r}(b)-g_\theta(a)C_{q,r}(a)
  -\int_{(a,b]}g'_\theta(t)C_{q,r}(t)\,dt.
\]

This is `progression_quadratic_abel`; `squareResidueSum_abel` rewrites
its left side as the actual square residue sum. Every differentiability
and derivative-integrability obligation is discharged using the proved
phase lemmas. The step-function prefix is the genuine floor-indexed
prefix from the Abel theorem.

Taking a=N/2 and b=N, with N natural, yields

\[
 \sum_{\substack{N/2<n\leq N\\n\equiv r\pmod q}}
     \Lambda(n)e(-n^2\theta)
 =g_\theta(N)C_{q,r}(N)-g_\theta(N/2)C_{q,r}(N/2)
  -\int_{(N/2,N]}g'_\theta(t)C_{q,r}(t)\,dt.
\]

`annularMangoldtResidue_abel` proves this identity with the real lower
endpoint N/2. The natural cutoff agrees because floor((N:R)/2)=N/2
in natural division; that equality is explicitly used. Thus odd N and
N=0 are covered, without substituting a half-subtraction identity that
requires an even cutoff. The residue sum is unnormalized; the 1/N factor
is not inserted or canceled at this stage.

## Files and remaining scope

| Module | New named theorems | Result |
|---|---:|---|
| QuadraticOscillation.lean | 10 | Actual phase, derivative, norm, continuity and integrability |
| ProgressionAbel.lean | 6 | Actual Lambda progression prefixes, residue identification and exact real-endpoint Abel formula |

The next unit subtracts a differentiable model and bounds the resulting
weighted prefix error, retaining both endpoints and the derivative
contribution. The source model x/phi(q)-chi(r)x^beta/(beta*phi(q)) and
its actual oscillatory integrals will then be specialized explicitly.
The analytic prefix bound itself remains a separate published input
boundary. No such theorem or own-paper deduction is assumed here.

<!-- checkpoint-verification -->

## Verification

All 86 project modules and the root were freshly rebuilt: 3601 jobs pass without warnings/errors. All 717 named theorems pass the complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound. The source scan checks 88 Lean files. Exact unique import/audit coverage and unchanged frozen source hashes are checked before packaging. There are no placeholders or added mathematical axioms.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. No new deep analytic input or own-paper lemma is assumed.

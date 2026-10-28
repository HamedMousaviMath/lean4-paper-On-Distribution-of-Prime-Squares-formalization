# Quantitative transport of the actual progression-prefix error

Checkpoint 25. This unit turns a bound on the actual progression prefix
into a bound on the quadratically weighted residue sum. It proves the
integration-by-parts deduction; the progression distribution estimate
itself remains an explicit input boundary.

## Prefix-error integral

Let g(t)=exp(-2*pi*i*theta*t^2), as constructed previously. Suppose
0<=a<=b<=N and R is a complex function satisfying |R(t)|<=B on [a,b].
The exact derivative bound gives

\[
 \left|\int_{(a,b]} g'(t)R(t)\,dt\right|
 \leq 4\pi|\theta|NB(b-a).
\]

Both endpoint terms have norm at most B, because |g|=1. The triangle
inequality therefore proves

\[
 |g(b)R(b)-g(a)R(a)-\int_{(a,b]}g'(t)R(t)\,dt|
 \leq B\bigl(2+4\pi|\theta|N(b-a)\bigr)
 \leq B\bigl(2+4\pi|\theta|N^2\bigr).
\]

The last inequality uses b-a<=N and B>=0. The explicit 2 is the sum
of two endpoint bounds. The integral estimate uses Mathlib's actual
Bochner integral norm bound. No differentiability assumption on the
prefix-error function is needed.

## Subtracting a differentiable model

Let C(t) be the actual complex progression von Mangoldt prefix from
`progressionMangoldtPrefix`. Let H,H' be complex functions such that
H has derivative H' at every point of [a,b], and H' is interval-integrable.
All these regularity conditions will be discharged for the source model
in the next unit.

We first prove integrability of g'(t)C(t), using Mathlib's theorem for
a smooth factor times a floor-indexed finite prefix. Continuity of H and
integrability of g' give integrability of g'H. Thus subtracting their
integrals is justified, rather than used as a formal rule without its
hypotheses.

Integration by parts for gH gives

\[
 \int_{(a,b]}g(t)H'(t)\,dt
 =g(b)H(b)-g(a)H(a)-\int_{(a,b]}g'(t)H(t)\,dt.
\]

Subtract this from the actual Abel identity proved in checkpoint 24:

\[
 W_r-\int_{(a,b]}g(t)H'(t)\,dt
 =g(b)(C(b)-H(b))-g(a)(C(a)-H(a))
  -\int_{(a,b]}g'(t)(C(t)-H(t))\,dt.
\]

`squareResidueSum_model_error_identity` proves this exact identity. W_r
is the actual unnormalized residue sum with the floor cutoffs at a,b.
It includes all von Mangoldt prime powers and the paper's negative phase.

Applying the prefix-error bound with R=C-H proves

\[
 |W_r-\int gH'|\leq B(2+4\pi|\theta|N^2).
\]

The hypothesis is a bound on the genuine unweighted prefix C-H; no
weighted-residue estimate or own-paper lemma is assumed.

## Annular normalization

Take a=N/2, b=N with N>=1. If the actual prefix difference is bounded
by N*delta throughout [N/2,N], then the normalized residue error is

\[
 \left|\frac{W_r}{N}-\frac1N\int_{N/2}^{N}g(t)H'(t)\,dt\right|
 \leq\delta(2+4\pi|\theta|N^2).
\]

`annularProgressionModel_error_bound` proves this statement. The real
lower endpoint and natural floor cutoff are matched explicitly. Positivity
of N justifies cancellation of 1/N against the prefix error N*delta.
No additional N factor is lost. Delta>=0 is displayed.

## Files

| Module | New named theorems | Result |
|---|---:|---|
| PrefixErrorBounds.lean | 2 | Endpoint plus derivative error bounds, including the N^2 version |
| ProgressionModelError.lean | 4 | Actual prefix-product integrability, exact model subtraction, quantitative and normalized annular bounds |

The next unit proves regularity and the derivative of the source model
x/phi(q)-z*x^beta/(beta*phi(q)), for beta>0 on a positive interval,
and identifies its integral with the actual ordinary and exceptional
oscillatory integrals. The raw progression-prefix estimate remains an
explicit analytic boundary. The final R^-5 and minor-arc statements of
Lemma 6.5 are not concluded here.

<!-- checkpoint-verification -->

## Verification

All 88 project modules and the root were freshly rebuilt: 3603 jobs pass without warnings/errors. All 723 named theorems pass the complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound. The source scan checks 90 Lean files. Exact unique import/audit coverage and unchanged frozen source hashes are checked before packaging. There are no placeholders or added mathematical axioms.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. No new deep analytic input or own-paper lemma is assumed.

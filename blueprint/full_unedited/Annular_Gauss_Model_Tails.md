# Uniform tails for the actual Gauss models

The model is
\[
G_{N,q,\chi,\kappa,\beta,a}(\theta)
=\mathfrak s(a,q)M_N^1(\theta)
-\mathfrak s_\chi(a,q)\kappa M_N^\beta(\theta).
\]
It uses the project's genuine totient-normalized sums and the genuine annular integrals, with the source sign and phase.

The already proved unconditional bound for all complex Dirichlet characters, applied at epsilon=1/12, gives one constant C such that both Gauss coefficients are at most \(Cq^{-5/12}\) for unit a. The principal coefficient is the character-one specialization of the same proved theorem.

For \(N\ge2,\ 0\le\beta\le1,\ |\kappa|\le1\), the half bound for each integral gives
\[
|G(\theta)|\le Cq^{-5/12}.
\]
If \(q\le R\) and \(|\theta|\ge R/(qN^2)\), each integral is at most \(2q/(\pi R)\), so
\[
|G(\theta)|\le (4C/\pi)R^{-5/12}.
\]
The required power comparison \(q^{-5/12}q/R\le R^{-5/12}\) is proved with positive bases. Multiplication by the actual cutoff \(\eta_s\in[0,1]\) does not increase the norm.

| Module | New named theorems |
| --- | ---: |
| AnnularGaussModelBounds.lean | 5 |

## Scope

All inputs used here are proved in the pinned project or Mathlib. No new external analytic estimate is assumed. The coefficient kappa remains a parameter with norm at most one; the exceptional-conductor indicator will be an allowed specialization. This is a model-tail result, not a minor-arc bound for the actual prime sum, and it does not complete the global approximation.

<!-- checkpoint-verification -->

## Verification

All 103 project modules and the root were freshly rebuilt: 3622 jobs pass without warnings/errors. All 818 named theorems pass the complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound. The source scan checks 105 Lean files. Exact unique import/audit coverage and unchanged frozen source hashes are checked before packaging. There are no placeholders or added mathematical axioms.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. No new deep analytic input or own-paper lemma is assumed.

# Bounding the actual integration-by-parts terms

For \(W_\beta(t)=t^{\beta-2}\) and \(E_\theta(t)=e^{-2\pi i\theta t^2}\), the previous identity reduces decay to the boundary
\([W_\beta(t)E_\theta(t)]_{N/2}^N\) and remainder
\(\int_{N/2}^N W_\beta'(t)E_\theta(t)\,dt\).

For \(N\ge2,\ 0\le\beta\le1\), every t in the annulus is at least one. Monotonicity in the exponent and in the positive base gives
\[
 |W_\beta(t)|\le 2/N,\qquad
 |W_\beta'(t)|\le 8/N^2.
\]
The first estimate only requires beta<=1. The second also uses beta>=0 to bound \(|\beta-2|\) by two. The oscillation has norm one.

The triangle inequality bounds the two boundary terms together by \(4/N\). The annulus has length \(N/2\), so bounding the remainder integrand by \(8/N^2\) also gives \(4/N\). These estimates concern the actual integrals, with no hypothesis asserting their decay.

| Module | New named theorems |
| --- | ---: |
| AnnularBoundaryBounds.lean | 7 |

## Scope

The proof is unconditional. The next unit will combine these bounds with exact integration by parts and the normalization 1/N. This is a supporting step toward the source model estimates; it does not complete the full minor-arc lemma or the high-low decomposition.

<!-- checkpoint-verification -->

## Verification

All 99 project modules and the root were freshly rebuilt: 3614 jobs pass without warnings/errors. All 789 named theorems pass the complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound. The source scan checks 101 Lean files. Exact unique import/audit coverage and unchanged frozen source hashes are checked before packaging. There are no placeholders or added mathematical axioms.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. No new deep analytic input or own-paper lemma is assumed.

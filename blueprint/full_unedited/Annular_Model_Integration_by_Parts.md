# Exact integration by parts on the quadratic annulus

Write \(E_\theta(t)=e^{-2\pi i\theta t^2}\), \(W_\beta(t)=t^{\beta-2}\), and \(K_\theta=-4\pi i\theta\). For \(N\ge1\), all powers in this proof are evaluated on \([N/2,N]\subset(0,\infty)\).

The new module proves the derivatives and integrability needed for the exact complex identity
\[
K_\theta\int_{N/2}^N t^{\beta-1}E_\theta(t)\,dt
=[t^{\beta-2}E_\theta(t)]_{N/2}^{N}
-\int_{N/2}^N(\beta-2)t^{\beta-3}E_\theta(t)\,dt.
\]
It holds for every real beta and theta. The normalization \(1/N\) is not yet applied in this identity. Multiplying by \(K_\theta\) instead of dividing by it keeps zero frequency within the statement.

The power identity \(t^{\beta-2}t=t^{\beta-1}\) is justified for positive real t. No periodicity is assumed for a noninteger integration variable, and the genuine phase derivative from QuadraticOscillation.lean is used.

| Module | New named theorems |
| --- | ---: |
| AnnularModelIntegrationByParts.lean | 6 |

## Scope

These are unconditional calculus proofs. Bounds for the two boundary terms and the remainder integral are the next step. The full minor-arc deduction and the analytic decomposition remain open. This unit requests no manuscript change.

<!-- checkpoint-verification -->

## Verification

All 98 project modules and the root were freshly rebuilt: 3613 jobs pass without warnings/errors. All 782 named theorems pass the complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound. The source scan checks 100 Lean files. Exact unique import/audit coverage and unchanged frozen source hashes are checked before packaging. There are no placeholders or added mathematical axioms.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. No new deep analytic input or own-paper lemma is assumed.

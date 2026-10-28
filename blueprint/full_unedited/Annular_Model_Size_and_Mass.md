# Uniform bounds and mass for the actual annular models

This unit concerns the integral already used in the genuine major-arc formula:
\[
 M_N^\beta(\theta)=\frac1N\int_{N/2}^N t^{\beta-1}
             e^{-2\pi i\theta t^2}\,dt.
\]
The endpoints are real, including when \(N\) is odd. The integral is not replaced by a discrete sum or by an abstract bounded function.

For \(N\ge1\) and \(\beta\le1\), the power density decreases on this positive annulus. Since the oscillation has norm one,
\[
 |M_N^\beta(\theta)|\le\tfrac12(N/2)^{\beta-1}.
\]
Consequently \(N\ge2,\ \beta\le1\) gives the uniform bound \(1/2\), including the ordinary case \(\beta=1\). Positivity of beta is not needed for these size bounds because the interval is bounded away from zero.

For \(\beta>0\), the derivative of \(t^\beta/\beta\) gives the exact identity
\[
 M_N^\beta(0)=\frac{N^\beta-(N/2)^\beta}{N\beta}.
\]
The Lean proof uses the previously proved derivative, proves interval integrability on the positive annulus, and applies the complex-valued fundamental theorem of calculus.

| Module | New named theorems |
| --- | ---: |
| AnnularModelSize.lean | 5 |

## Scope

No external analytic input is used. This proves the uniform-size part needed in the approximation argument; frequency decay is the next task. The full source minor-arc deduction remains unresolved as documented in Ren_Input_and_Annular_Bound.md. No manuscript modification is requested by this unit.

<!-- checkpoint-verification -->

## Verification

All 97 project modules and the root were freshly rebuilt: 3612 jobs pass without warnings/errors. All 776 named theorems pass the complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound. The source scan checks 99 Lean files. Exact unique import/audit coverage and unchanged frozen source hashes are checked before packaging. There are no placeholders or added mathematical axioms.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. No new deep analytic input or own-paper lemma is assumed.

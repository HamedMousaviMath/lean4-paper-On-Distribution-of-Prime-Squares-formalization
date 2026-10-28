# Checkpoint 756: Sum polynomially weighted sharp cutoff profiles uniformly

For every positive decay exponent and every fixed polynomial degree, the two-sided dyadic cutoff profile is summable even after multiplication by (s+1)^m. Its total is bounded uniformly by an explicit constant times (1+log W)^m for W >= 1. The proof splits at a genuine dyadic scale adjacent to W, uses the previously verified uniform profile sum for the lower part, and sums a polynomial times a geometric sequence for the upper part. This provides the sharp arithmetic summation needed after the cubic logarithmic block loss, without weakening the Q^(-1/2) leading power.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| PolynomialDyadicProfileSum.lean | 4 |

- `shifted_polynomial_geometric_summable`
- `polynomialDyadicProfileConstant_nonneg`
- `polynomial_dyadic_profile_summable`
- `polynomial_dyadic_profile_tsum`

<!-- checkpoint-verification -->

## Verification

All 823 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4430-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2046 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 825 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results under their paper hypotheses remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. In addition, Lemma 3.21 and BOTH conclusions of Theorem 1.1 are complete checked implications under their explicit independent deep inputs. The PNT limits are used in the sharp Gauss/high bound; an imported PNT bridge is not integrated. The whole paper, the full maximal clauses of Proposition 4.19/6.21 and the later headline applications remain unfinished. See docs/THEOREM_1_1_EXTERNAL_INPUTS.md. PNT limits, raw compatible progression/Ren/Ghosh data, and the independent square decomposition remain explicit hypotheses. The smooth multifrequency boundary is only for later maximal applications.

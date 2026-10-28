# Checkpoint 789: Every error exponent with one fixed source range and operator family

The actual selected error operator now satisfies Q^(-1/2)(1+log N)^(-A) decay for every real A>=0, with one positive source-cutoff coefficient chosen before A. The same operator uses the same N,Q-dependent Page datum for every exponent. Large N uses the existing proved all-point circle approximation from raw progression/Ren/Ghosh data; the finitely many smaller arithmetic scales use the unconditional envelope from checkpoint788. Geometry bounds Q by the finite threshold, allowing the constant depending on A to absorb those scales. Thus no A-dependent narrowing of the final source range or A-dependent replacement of the error operator is used. The resulting bound has logarithmic Q power zero, which implies the source's allowed polynomial-logarithmic loss. Raw data existence remains the explicit refined independent input, not an assumed error estimate. This completes the error component needed by Proposition 4.19 without awarding the separate stronger source approximation lemma, whose full statement has not been reviewed here.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| SelectedPrimeErrorBounds.lean | 1 |

- `selectedPrimeError_all_exponents`

<!-- checkpoint-verification -->

## Verification

All 856 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4463-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2210 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 858 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results under their paper hypotheses remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. In addition, Lemma 3.21 and BOTH conclusions of Theorem 1.1 are complete checked implications under their explicit independent deep inputs. The PNT limits are used in the sharp Gauss/high bound; an imported PNT bridge is not integrated. Both source clauses of Proposition 6.21 are also complete checked implications under their recorded independent inputs. The whole paper, Proposition 4.19 and the later headline applications remain unfinished. See docs/THEOREM_1_1_EXTERNAL_INPUTS.md. PNT limits, raw compatible progression/Ren/Ghosh data, and the global independent square decomposition remain explicit hypotheses. Reflection between plus and minus square translations is proved without any extra analytic assumption. The smooth multifrequency boundary is only for later maximal applications.

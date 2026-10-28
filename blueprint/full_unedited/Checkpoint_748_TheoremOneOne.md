# Checkpoint 748: Theorem 1.1: both conclusions and exact real-exponent statement

Completes the combined export PrimeSquares.theorem_1_1 and the literal real-exponent/sum-of-powers form of the second conclusion, including actual output membership in l^{p'}. Both statements are for the genuine full von-Mangoldt square average, all positive integer arithmetic cutoffs, exact source interval cardinality, every restricted coefficient cstar>4*sqrt(3)/9, and every real 3/2<p<=2. The strong estimate is proved for all lp inputs, hence includes the manuscript's supported inputs. The source-to-Lean quantifier review awards Theorem1.1 status CONDITIONAL: a complete implication under the explicit PNT limits, raw compatible progression/Ren/Ghosh data existence, and the independent ordinary-square decomposition plus its globalization/reflection. None is a new Lean axiom or an assumed prime-square conclusion. The separate maximal/sparse and later paper results remain unfinished. Canonical paper coverage and remaining-work reports are updated with this reviewed milestone.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| TheoremOneOne.lean | 4 |

- `normalized_lp_norm_as_sum`
- `theorem_1_1_strong_sum`
- `theorem_1_1_strong_real`
- `theorem_1_1`

<!-- checkpoint-verification -->

## Verification

All 815 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4422-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2021 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 817 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results under their paper hypotheses remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. In addition, Lemma 3.21 and BOTH conclusions of Theorem 1.1 are complete checked implications under their explicit independent deep inputs. The PNT limits are used in the sharp Gauss/high bound; an imported PNT bridge is not integrated. The whole paper, the full maximal clauses of Proposition 4.19/6.21 and the later headline applications remain unfinished. See docs/THEOREM_1_1_EXTERNAL_INPUTS.md. PNT limits, raw compatible progression/Ren/Ghosh data, and the independent square decomposition remain explicit hypotheses. The smooth multifrequency boundary is only for later maximal applications.

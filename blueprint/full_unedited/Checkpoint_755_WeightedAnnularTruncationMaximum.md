# Checkpoint 755: Complete the actual annular maximum with changing denominator cutoffs

The actual weighted annular-source block now has a proved joint maximum over every dyadic scale from M >= 2 and every real upper denominator cutoff. For s >= 4 and coefficients bounded by A, the majorant has l2 norm at most K(C) A(s+1)^3 times the input norm. Its only analytic boundary is the previously explicit general smooth multifrequency input. The proof constructs disjoint wider source cutoffs, localizes the actual symbols, derives the hereditary time estimate from the all-starting-scale theorem, and applies the checked denominator-truncation theorem and cardinality budget. This supplies the formerly missing actual-source interval estimate without assuming a maximal statement from this paper.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| WeightedAnnularTruncationMaximum.lean | 1 |

- `weightedAnnular_truncation_maximum`

<!-- checkpoint-verification -->

## Verification

All 822 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4429-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2042 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 824 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results under their paper hypotheses remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. In addition, Lemma 3.21 and BOTH conclusions of Theorem 1.1 are complete checked implications under their explicit independent deep inputs. The PNT limits are used in the sharp Gauss/high bound; an imported PNT bridge is not integrated. The whole paper, the full maximal clauses of Proposition 4.19/6.21 and the later headline applications remain unfinished. See docs/THEOREM_1_1_EXTERNAL_INPUTS.md. PNT limits, raw compatible progression/Ren/Ghosh data, and the independent square decomposition remain explicit hypotheses. The smooth multifrequency boundary is only for later maximal applications.

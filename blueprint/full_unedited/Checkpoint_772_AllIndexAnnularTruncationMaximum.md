# Checkpoint 772: Complete the actual annular maximum at every denominator index

The actual annular joint scale-and-denominator-cutoff maximum is now proved for every denominator index, including 0, 1, 2 and 3. The small indices use the verified cutoff comparison, a geometric error maximum, and the separated index-4 source estimate. A concrete finite cardinality bound controls the small center sets. Together with the previously proved large-index maximum, this yields one constant times A(s+1)^3 for every index, every starting M >= 2, every allowed beta sequence, and every nonnegative changing denominator radius. This closes the small-frequency issue required to prove a uniform bounded-Q high maximum.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| AllIndexAnnularTruncationMaximum.lean | 6 |

- `dyadic_inverse_square_bound`
- `geometric_symbol_maximum`
- `weightedSmallSource_difference_bound`
- `allIndexAnnularConstant_pos`
- `smallIndex_annular_truncation_maximum`
- `allIndex_annular_truncation_maximum`

<!-- checkpoint-verification -->

## Verification

All 839 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4446-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2108 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 841 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results under their paper hypotheses remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. In addition, Lemma 3.21 and BOTH conclusions of Theorem 1.1 are complete checked implications under their explicit independent deep inputs. The PNT limits are used in the sharp Gauss/high bound; an imported PNT bridge is not integrated. The whole paper, the full maximal clauses of Proposition 4.19/6.21 and the later headline applications remain unfinished. See docs/THEOREM_1_1_EXTERNAL_INPUTS.md. PNT limits, raw compatible progression/Ren/Ghosh data, and the independent square decomposition remain explicit hypotheses. The smooth multifrequency boundary is only for later maximal applications.

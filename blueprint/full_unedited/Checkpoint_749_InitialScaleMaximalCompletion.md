# Checkpoint 749: Complete a maximal estimate across finitely many initial scales

Proves the operator-level extension from a dominated infinite tail to all natural time indices, with a finite initial-scale cost and an actual nonnegative real-l2 majorant. This is the precise completion step needed to remove the starting-scale restrictions in the existing annular multifrequency bound. It introduces no deep hypothesis. Checkpoint748 and both Theorem1.1 conclusions are recovered and retained unchanged; the full project is freshly rebuilt after workspace maintenance. Proposition6.21 remains open until the actual annular family, truncations, sharp arithmetic and exceptional-character assembly are proved.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| InitialScaleMaximalCompletion.lean | 1 |

- `initialScale_maximal_completion`

<!-- checkpoint-verification -->

## Verification

All 816 project modules and the root were freshly rebuilt: 4423 jobs pass without warnings/errors. All 2022 named theorems pass the complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound. The source scan checks 818 Lean files. Exact unique import/audit coverage and unchanged frozen source hashes are checked before packaging. There are no placeholders or added mathematical axioms.

The ten completed numbered results under their paper hypotheses remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. In addition, Lemma 3.21 and BOTH conclusions of Theorem 1.1 are complete checked implications under their explicit independent deep inputs. The PNT limits are used in the sharp Gauss/high bound; an imported PNT bridge is not integrated. The whole paper, the full maximal clauses of Proposition 4.19/6.21 and the later headline applications remain unfinished. See docs/THEOREM_1_1_EXTERNAL_INPUTS.md. PNT limits, raw compatible progression/Ren/Ghosh data, and the independent square decomposition remain explicit hypotheses. The smooth multifrequency boundary is only for later maximal applications.

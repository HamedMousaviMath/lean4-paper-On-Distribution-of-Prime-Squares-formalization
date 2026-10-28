# Checkpoint 782: Reflection transfers actual maximal bounds and temporal majorants

Spatial reflection transfers arbitrary families of lp-to-lq maps, including the l-infinity endpoint. The new LpFamilyMaximalBound predicate requires bounded coordinate norm ranges, an actual real-valued lp representative of their supremum, and the stated norm bound. The proof reflects that representative and proves equivalence of the maximal estimate for T_i and R T_i R with the same constant. No summability of operator norms or additional analytic maximal theorem is assumed. The already-used FiniteTemporalMajorants predicate is likewise equivalent for a family and its spatial reflection. Norms of operator-output differences are also preserved, recording the algebraic ingredient for variation and difference estimates without claiming to formalize a separate variational theorem. All these results are unconditional transfer lemmas. The independent ordinary-square analytic theorem and its globalization remain external until separately proved; this checkpoint supplies no new analytic assumption.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| MaximalReflection.lean | 6 |

- `familySupremum_reflect`
- `lpFamilyMaximalBound_reflect`
- `lpFamilyMaximalBound_reflect_iff`
- `finiteTemporalMajorants_reflect`
- `finiteTemporalMajorants_reflect_iff`
- `reflectedMap_difference_norm`

<!-- checkpoint-verification -->

## Verification

All 849 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4456-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2179 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 851 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results under their paper hypotheses remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. In addition, Lemma 3.21 and BOTH conclusions of Theorem 1.1 are complete checked implications under their explicit independent deep inputs. The PNT limits are used in the sharp Gauss/high bound; an imported PNT bridge is not integrated. Both source clauses of Proposition 6.21 are also complete checked implications under their recorded independent inputs. The whole paper, Proposition 4.19 and the later headline applications remain unfinished. See docs/THEOREM_1_1_EXTERNAL_INPUTS.md. PNT limits, raw compatible progression/Ren/Ghosh data, and the independent square decomposition remain explicit hypotheses. The smooth multifrequency boundary is only for later maximal applications.

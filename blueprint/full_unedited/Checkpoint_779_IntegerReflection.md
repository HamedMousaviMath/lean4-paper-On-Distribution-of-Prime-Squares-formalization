# Checkpoint 779: Integer reflection is an involutive lp isometry and reverses support intervals

Spatial reflection is defined by Rf(x)=f(-x). The new IntegerReflection module proves membership in every lp space is preserved, reflection is involutive, and its norm is unchanged for every p>=1, including p=infinity. It constructs an actual linear isometric equivalence over any normed scalar field, so the real and complex sequence spaces used by the paper are both covered. It also proves that finite input functions and finite indicators reflect exactly, that finite-set cardinalities are preserved, and that the integer interval [a,b] becomes [-b,-a]. These are unconditional algebraic and sequence-space proofs; the independent square-average theorem is not assumed or formalized here. This checkpoint is the foundation for the convolution and square-sign transfer. The completed conditional Theorem 1.1 and Proposition 6.21 are retained. A stale generated progress paragraph was corrected to agree with the already-verified Proposition 6.21 completion. The manuscript and all accepted replacements are unchanged.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| IntegerReflection.lean | 13 |

- `reflectSequence_apply`
- `reflectSequence_involutive`
- `memLp_reflectSequence`
- `reflectLp_apply`
- `reflectLp_involutive`
- `reflectLp_norm`
- `integerReflection_apply`
- `mem_reflectedFinset`
- `reflectedFinset_involutive`
- `reflectedFinset_card`
- `reflectedFinset_Icc`
- `reflectLp_finiteIndicator`
- `reflectLp_finiteInput`

<!-- checkpoint-verification -->

## Verification

All 846 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4453-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2136 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 848 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results under their paper hypotheses remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. In addition, Lemma 3.21 and BOTH conclusions of Theorem 1.1 are complete checked implications under their explicit independent deep inputs. The PNT limits are used in the sharp Gauss/high bound; an imported PNT bridge is not integrated. Both source clauses of Proposition 6.21 are also complete checked implications under their recorded independent inputs. The whole paper, Proposition 4.19 and the later headline applications remain unfinished. See docs/THEOREM_1_1_EXTERNAL_INPUTS.md. PNT limits, raw compatible progression/Ren/Ghosh data, and the independent square decomposition remain explicit hypotheses. The smooth multifrequency boundary is only for later maximal applications.

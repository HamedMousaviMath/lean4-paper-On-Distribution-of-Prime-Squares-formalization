# Checkpoint 762: Complete the sharp maximum for the actual ordinary and fixed-character families

The countable sharp theorem is instantiated for the two actual arithmetic families. The ordinary part uses the principal quadratic Gauss coefficient; the exceptional part uses the induced fixed real character, the exact quotient denominator q/q_chi, and its conductor-sensitive coefficient bound. The exceptional bound retains sigma_chi sqrt(B_chi), rather than discarding its decay. A proved mask identity handles both the active and inactive exceptional selectors and restricts the active sum exactly to conductor multiples. The upper denominator radius may change arbitrarily with scale.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| SharpOrdinaryExceptionalMaximum.lean | 3 |

- `sharpOrdinary_source_maximum`
- `sharpExceptional_source_maximum`
- `thresholdAnnularBlock_mask`

<!-- checkpoint-verification -->

## Verification

All 829 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4436-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2068 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 831 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results under their paper hypotheses remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. In addition, Lemma 3.21 and BOTH conclusions of Theorem 1.1 are complete checked implications under their explicit independent deep inputs. The PNT limits are used in the sharp Gauss/high bound; an imported PNT bridge is not integrated. The whole paper, the full maximal clauses of Proposition 4.19/6.21 and the later headline applications remain unfinished. See docs/THEOREM_1_1_EXTERNAL_INPUTS.md. PNT limits, raw compatible progression/Ren/Ghosh data, and the independent square decomposition remain explicit hypotheses. The smooth multifrequency boundary is only for later maximal applications.

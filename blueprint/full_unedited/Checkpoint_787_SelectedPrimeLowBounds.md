# Checkpoint 787: Both low clauses on every l1 input with an absolute source range

Both actual low-term clauses of Proposition 4.19 are now proved for the common selected operator family, on every l1 input. One positive absolute source-cutoff coefficient is chosen before all data, epsilons and error exponents. The exact l1-to-l-infinity norm is bounded by (2 lowSpatialConstant) N^-2 Q log(2Q), and the pointwise local bound by (8 lowSpatialConstant) Q log(2Q) times the literal all-real-radius sourceLocalMass. The latter is the printed source supremum with C=1. A proved general cutoff-forcing lemma shows that a sufficiently small fixed coefficient in log Q<=delta sqrt(log N), together with Q>=2, forces any fixed starting threshold. This handles the low-term threshold without weakening the source N-range. No own-paper low estimate or local-to-global assertion is assumed. The existing raw number-theoretic boundary remains explicit, and no manuscript replacement is needed.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| SelectedPrimeLowBounds.lean | 2 |

- `cutoff_forcing_threshold`
- `selectedPrimeLow_source_bounds`

<!-- checkpoint-verification -->

## Verification

All 854 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4461-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2206 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 856 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results under their paper hypotheses remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. In addition, Lemma 3.21 and BOTH conclusions of Theorem 1.1 are complete checked implications under their explicit independent deep inputs. The PNT limits are used in the sharp Gauss/high bound; an imported PNT bridge is not integrated. Both source clauses of Proposition 6.21 are also complete checked implications under their recorded independent inputs. The whole paper, Proposition 4.19 and the later headline applications remain unfinished. See docs/THEOREM_1_1_EXTERNAL_INPUTS.md. PNT limits, raw compatible progression/Ren/Ghosh data, and the global independent square decomposition remain explicit hypotheses. Reflection between plus and minus square translations is proved without any extra analytic assumption. The smooth multifrequency boundary is only for later maximal applications.

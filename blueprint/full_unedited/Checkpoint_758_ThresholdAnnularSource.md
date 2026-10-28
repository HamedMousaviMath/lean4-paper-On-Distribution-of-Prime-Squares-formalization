# Checkpoint 758: Identify the actual high operator with the common threshold-annular family

The ordinary and exceptional pieces of the actual high symbol are identified exactly with a common threshold-annular family. Below the effective cutoff this family is the actual narrow-cutoff collar; above it the family is the actual broad annular source. This identity is proved for each source term and for the full finite high model, with the exceptional effective threshold Q q_chi/B_chi. A separate exact identity writes an arbitrary varying upper denominator cutoff in a collar block as a time-dependent coefficient bounded by the original coefficient. No maximal estimate is built into these definitions.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| ThresholdAnnularSource.lean | 5 |

- `circleHighTerm_threshold_ordinary`
- `circleExceptionalHigh_threshold`
- `circleHighModel_threshold_decomposition`
- `thresholdAnnularBlock_split`
- `rationalCollarBlock_truncation`

<!-- checkpoint-verification -->

## Verification

All 825 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4432-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2058 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 827 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results under their paper hypotheses remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. In addition, Lemma 3.21 and BOTH conclusions of Theorem 1.1 are complete checked implications under their explicit independent deep inputs. The PNT limits are used in the sharp Gauss/high bound; an imported PNT bridge is not integrated. The whole paper, the full maximal clauses of Proposition 4.19/6.21 and the later headline applications remain unfinished. See docs/THEOREM_1_1_EXTERNAL_INPUTS.md. PNT limits, raw compatible progression/Ren/Ghosh data, and the independent square decomposition remain explicit hypotheses. The smooth multifrequency boundary is only for later maximal applications.

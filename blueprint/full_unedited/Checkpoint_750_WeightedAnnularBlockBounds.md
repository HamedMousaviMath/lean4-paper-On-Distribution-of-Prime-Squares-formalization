# Checkpoint 750: Bound each actual annular block uniformly at the initial scales

The actual annular source on the circle has a uniform pointwise bound. Its support lies inside the source cutoff, and distinct canonical centers in one sufficiently separated denominator block give disjoint supports. Consequently a fixed weighted annular block, with coefficients bounded by A, has multiplier operator norm at most (3/2)A, uniformly in the starting scale. These are bounds for the actual periodized oscillatory-integral symbols. They supply the finite initial-scale part of the maximal argument; they do not assert Proposition 6.21.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| WeightedAnnularBlockBounds.lean | 4 |

- `circleAnnularSource_norm_bound`
- `circleAnnularSource_zero_of_cutoff`
- `weightedAnnularSourceBlock_norm_bound`
- `weightedAnnularSourceBlock_operator_bound`

<!-- checkpoint-verification -->

## Verification

All 817 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4424-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2026 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 819 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results under their paper hypotheses remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. In addition, Lemma 3.21 and BOTH conclusions of Theorem 1.1 are complete checked implications under their explicit independent deep inputs. The PNT limits are used in the sharp Gauss/high bound; an imported PNT bridge is not integrated. The whole paper, the full maximal clauses of Proposition 4.19/6.21 and the later headline applications remain unfinished. See docs/THEOREM_1_1_EXTERNAL_INPUTS.md. PNT limits, raw compatible progression/Ren/Ghosh data, and the independent square decomposition remain explicit hypotheses. The smooth multifrequency boundary is only for later maximal applications.

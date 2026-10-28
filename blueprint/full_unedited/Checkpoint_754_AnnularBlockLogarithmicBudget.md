# Checkpoint 754: Bound the actual frequency and truncation losses by a cubic logarithm

The frequency-cardinality loss is now bounded by the denominator-block index: (1+log(card Gamma+1))^2 <= 36(s+1)^2 for canonical centers of denominator at most 2^(s+1). The proof uses the actual finite enumeration bound, not an asymptotic cardinality assumption. Combining this with the finite initial-scale loss and the denominator-truncation factor gives an explicit constant K(C)=3(8+18C+E) multiplying A(s+1)^3. This fixed cubic logarithmic cost is harmless in the final sharp-exponent asymptotic, but no sharper auxiliary logarithmic exponent is asserted.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| AnnularBlockLogarithmicBudget.lean | 4 |

- `circleFrequencyLogFactor_mono`
- `circleFrequencyLogFactor_denominator_budget`
- `annularTruncationConstant_nonneg`
- `annular_allStarting_budget`

<!-- checkpoint-verification -->

## Verification

All 821 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4428-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2041 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 823 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results under their paper hypotheses remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. In addition, Lemma 3.21 and BOTH conclusions of Theorem 1.1 are complete checked implications under their explicit independent deep inputs. The PNT limits are used in the sharp Gauss/high bound; an imported PNT bridge is not integrated. The whole paper, the full maximal clauses of Proposition 4.19/6.21 and the later headline applications remain unfinished. See docs/THEOREM_1_1_EXTERNAL_INPUTS.md. PNT limits, raw compatible progression/Ren/Ghosh data, and the independent square decomposition remain explicit hypotheses. The smooth multifrequency boundary is only for later maximal applications.

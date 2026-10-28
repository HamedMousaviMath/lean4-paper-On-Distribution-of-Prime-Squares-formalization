# Checkpoint 747: Theorem 1.1 strong conclusion for the actual averaging operator

Identifies the interpolated kernel realization with the genuine finite von-Mangoldt square average by uniqueness on finite indicators. Proves the sharp scaling for this ACTUAL lp-to-lq operator, and exports theorem_1_1_strong with the exact source interval cardinality and normalization, including p=2. The inequality holds for every lp input, so it includes all source-supported inputs. Both mathematical conclusions now have checked declarations (theorem_1_1_restricted and theorem_1_1_strong); the final combined statement, literal real-exponent/sum form and paper-level completion review are being prepared before awarding the Theorem 1.1 milestone. The explicit independent deep hypotheses remain unchanged.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| PrimeSquareActualStrongOperator.lean | 4 |

- `primeSquareImprovingOperator_apply`
- `primeSquare_actual_strong_uniform`
- `improving_scale_comparison`
- `theorem_1_1_strong`

<!-- checkpoint-verification -->

## Verification

All 814 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4421-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2017 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 816 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. See docs/THEOREM_1_1_EXTERNAL_INPUTS.md. PNT limits, raw compatible progression/Ren/Ghosh data, and the independent square decomposition remain explicit hypotheses. The smooth multifrequency boundary is only for later maximal applications.

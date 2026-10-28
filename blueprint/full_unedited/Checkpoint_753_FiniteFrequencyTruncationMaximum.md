# Checkpoint 753: Control time and denominator truncations using localized input energy

A general finite-frequency theorem now controls the maximum jointly over time and every real denominator cutoff. Its hypotheses are localization by pairwise disjoint cutoff symbols of norm at most one and a hereditary time-maximal estimate on each frequency subset. The proof groups the frequencies by denominator, constructs each interval majorant on the corresponding filtered input, applies the already proved time-dependent Rademacher-Menshov inequality, and uses multiplier Bessel orthogonality to recover the original input norm. The final loss is h+1 when the maximum denominator plus one is at most 2^h. In particular, it does not introduce a square-root loss in the number of denominators. This is a proved abstract transfer theorem, with the actual source-family instantiation still to follow.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| FiniteFrequencyTruncationMaximum.lean | 5 |

- `rationalCircle_interval_grouping`
- `finite_localized_symbol_sum`
- `rationalCircle_grouped_disjoint`
- `rationalCircle_grouped_norm`
- `finiteFrequency_denominator_maximum`

<!-- checkpoint-verification -->

## Verification

All 820 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4427-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2037 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 822 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results under their paper hypotheses remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. In addition, Lemma 3.21 and BOTH conclusions of Theorem 1.1 are complete checked implications under their explicit independent deep inputs. The PNT limits are used in the sharp Gauss/high bound; an imported PNT bridge is not integrated. The whole paper, the full maximal clauses of Proposition 4.19/6.21 and the later headline applications remain unfinished. See docs/THEOREM_1_1_EXTERNAL_INPUTS.md. PNT limits, raw compatible progression/Ren/Ghosh data, and the independent square decomposition remain explicit hypotheses. The smooth multifrequency boundary is only for later maximal applications.

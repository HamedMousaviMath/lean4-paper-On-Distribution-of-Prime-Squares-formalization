# Checkpoint 771: Control small denominator indices by a summable actual-cutoff difference

The small denominator indices are compared with the separated cutoff at index 4. The difference vanishes in the common central core and has actual multiplier norm at most an explicit constant divided by N^2, uniformly in beta in [0,1]. The proof uses the true source bump core, oscillatory-integral decay outside that core, and the finite circle-periodization norm bound. This summable error supplies a uniform treatment of the finitely many small denominator indices needed for the bounded-Q completion.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| SmallSourceCutoffDifference.lean | 3 |

- `smallSourceDifferenceConstant_pos`
- `localizedAnnularSource_small_difference`
- `circleAnnularSource_small_difference`

<!-- checkpoint-verification -->

## Verification

All 838 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4445-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2102 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 840 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results under their paper hypotheses remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. In addition, Lemma 3.21 and BOTH conclusions of Theorem 1.1 are complete checked implications under their explicit independent deep inputs. The PNT limits are used in the sharp Gauss/high bound; an imported PNT bridge is not integrated. The whole paper, the full maximal clauses of Proposition 4.19/6.21 and the later headline applications remain unfinished. See docs/THEOREM_1_1_EXTERNAL_INPUTS.md. PNT limits, raw compatible progression/Ren/Ghosh data, and the independent square decomposition remain explicit hypotheses. The smooth multifrequency boundary is only for later maximal applications.

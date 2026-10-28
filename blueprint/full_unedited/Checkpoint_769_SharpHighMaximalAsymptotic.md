# Checkpoint 769: Recover the precise leading-two asymptotic after all maximal losses

The analytic Q rate is converted to the precise leading-two asymptotic. Under the two explicit prime asymptotic inputs, for every epsilon > 0 there are fixed positive constants and a lower Q cutoff such that Q^(-1/2) exp(G(log Q)) (1+log Q)^3 is bounded by a constant times Q^(-1/2) exp((2+epsilon) sqrt(log Q)/log log Q). The same cutoff ensures all threshold-slope conditions needed by the maximal proof. The constants are independent of the starting scale, source radius, and exceptional data. This step does not claim the separate bounded-Q completion.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| SharpHighMaximalAsymptotic.lean | 1 |

- `sharpHighMaximalRate_asymptotic`

<!-- checkpoint-verification -->

## Verification

All 836 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4443-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2096 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 838 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results under their paper hypotheses remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. In addition, Lemma 3.21 and BOTH conclusions of Theorem 1.1 are complete checked implications under their explicit independent deep inputs. The PNT limits are used in the sharp Gauss/high bound; an imported PNT bridge is not integrated. The whole paper, the full maximal clauses of Proposition 4.19/6.21 and the later headline applications remain unfinished. See docs/THEOREM_1_1_EXTERNAL_INPUTS.md. PNT limits, raw compatible progression/Ren/Ghosh data, and the independent square decomposition remain explicit hypotheses. The smooth multifrequency boundary is only for later maximal applications.

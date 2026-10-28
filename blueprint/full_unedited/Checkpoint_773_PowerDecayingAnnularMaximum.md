# Checkpoint 773: Prove a uniform maximum for the full power-decaying annular family

The full bare annular family with denominator-dependent source indices now has a countable dyadic maximum whenever its fixed coefficients decay by any positive denominator power. The proof uses the all-index joint truncation estimate, the actual dyadic denominator partition, a convergent polynomial-geometric sum, and the verified finite-to-countable passage for the growing source radius. Any fixed lower-denominator restriction or conductor-multiple restriction may be included in the center set. The bound is uniform in the restriction, scale, and changing upper radius. This is the large-denominator input for the bounded-Q high estimate.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| PowerDecayingAnnularMaximum.lean | 3 |

- `annularPowerConstant_pos`
- `powerAnnular_finiteCenters_maximum`
- `powerAnnular_countable_maximum`

<!-- checkpoint-verification -->

## Verification

All 840 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4447-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2111 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 842 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results under their paper hypotheses remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. In addition, Lemma 3.21 and BOTH conclusions of Theorem 1.1 are complete checked implications under their explicit independent deep inputs. The PNT limits are used in the sharp Gauss/high bound; an imported PNT bridge is not integrated. The whole paper, the full maximal clauses of Proposition 4.19/6.21 and the later headline applications remain unfinished. See docs/THEOREM_1_1_EXTERNAL_INPUTS.md. PNT limits, raw compatible progression/Ren/Ghosh data, and the independent square decomposition remain explicit hypotheses. The smooth multifrequency boundary is only for later maximal applications.

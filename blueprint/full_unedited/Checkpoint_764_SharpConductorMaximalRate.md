# Checkpoint 764: Complete uniform sharp piece estimates with summable conductor decay

The ordinary countable maximum is now expressed as a constant times Q^(-1/2) exp(G(log Q)) (1+log Q)^3. The exceptional countable maximum has the same Q rate, uniformly above one fixed arithmetic cutoff, and retains a factor q_chi^(-1/50) after every conductor logarithm is absorbed. The constants and the lower cutoff are independent of the conductor, starting scale, denominator-radius sequence, input, and the allowed beta sequence. This is the summable estimate needed to combine different exceptional characters over time.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| SharpConductorMaximalRate.lean | 3 |

- `sharpHighMaximalRate_nonneg`
- `sharpOrdinary_rate_maximum`
- `sharpExceptional_conductor_rate`

<!-- checkpoint-verification -->

## Verification

All 831 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4438-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2076 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 833 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results under their paper hypotheses remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. In addition, Lemma 3.21 and BOTH conclusions of Theorem 1.1 are complete checked implications under their explicit independent deep inputs. The PNT limits are used in the sharp Gauss/high bound; an imported PNT bridge is not integrated. The whole paper, the full maximal clauses of Proposition 4.19/6.21 and the later headline applications remain unfinished. See docs/THEOREM_1_1_EXTERNAL_INPUTS.md. PNT limits, raw compatible progression/Ren/Ghosh data, and the independent square decomposition remain explicit hypotheses. The smooth multifrequency boundary is only for later maximal applications.

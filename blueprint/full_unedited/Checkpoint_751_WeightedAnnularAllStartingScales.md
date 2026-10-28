# Checkpoint 751: Complete the weighted annular maximum from every starting scale

The weighted annular-source maximum now holds from every starting scale M >= 2, under the existing general smooth multifrequency input. The proof chooses an explicit later starting scale 2^(2s+3) M at which both separation budgets hold, applies the previously checked infinite-tail result there, and adds the finitely many earlier operators using their actual uniform norm bound. The resulting loss is A times [(3/2)(2s+3)+(C/2)(1+log(card Gamma+1))^2+E]. No maximum, initial segment, or scale range is assumed as an extra input. The fixed polynomial logarithmic loss is compatible with the o(1) in Proposition 6.21; the stronger printed auxiliary logarithmic exponent is not claimed.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| WeightedAnnularAllStartingScales.lean | 2 |

- `annularLargeStart_budgets`
- `weightedAnnular_allStartingScales`

<!-- checkpoint-verification -->

## Verification

All 818 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4425-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2028 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 820 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results under their paper hypotheses remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. In addition, Lemma 3.21 and BOTH conclusions of Theorem 1.1 are complete checked implications under their explicit independent deep inputs. The PNT limits are used in the sharp Gauss/high bound; an imported PNT bridge is not integrated. The whole paper, the full maximal clauses of Proposition 4.19/6.21 and the later headline applications remain unfinished. See docs/THEOREM_1_1_EXTERNAL_INPUTS.md. PNT limits, raw compatible progression/Ren/Ghosh data, and the independent square decomposition remain explicit hypotheses. The smooth multifrequency boundary is only for later maximal applications.

# Checkpoint 785: Exact common low high and error operators on all inputs

Defines the actual low, high and error operators using one fixed optional Page datum and the manuscript radius sourceMajorArcScale N Q. None of these definitions depends on epsilon or an error exponent. Lean proves the exact continuous-linear-operator decomposition on all l2 inputs, not just indicators, using the exact annular Fourier identity. It also proves the identity on all l1 inputs with the low term realized as the genuine l1-to-l-infinity operator and the high/error inputs included into l2. The selected high tail is exactly the already verified dyadic source tail from Proposition 6.21, with the original starting-threshold mask and all dyadic scales at least two. This checkpoint establishes common operator identity and compatibility, without yet awarding any of the missing uniform bounds or closing Proposition 4.19. All existing completed results and the manuscript are preserved.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| SelectedPrimeSquareOperators.lean | 4 |

- `selectedPrimeLow_agreement`
- `selectedPrime_decomposition_l2`
- `selectedPrime_decomposition_l1`
- `selectedPrimeHighTail_of_le`

<!-- checkpoint-verification -->

## Verification

All 852 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4459-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2195 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 854 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results under their paper hypotheses remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. In addition, Lemma 3.21 and BOTH conclusions of Theorem 1.1 are complete checked implications under their explicit independent deep inputs. The PNT limits are used in the sharp Gauss/high bound; an imported PNT bridge is not integrated. Both source clauses of Proposition 6.21 are also complete checked implications under their recorded independent inputs. The whole paper, Proposition 4.19 and the later headline applications remain unfinished. See docs/THEOREM_1_1_EXTERNAL_INPUTS.md. PNT limits, raw compatible progression/Ren/Ghosh data, and the global independent square decomposition remain explicit hypotheses. Reflection between plus and minus square translations is proved without any extra analytic assumption. The smooth multifrequency boundary is only for later maximal applications.

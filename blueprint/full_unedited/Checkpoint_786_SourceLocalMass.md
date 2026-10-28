# Checkpoint 786: Literal real-radius local maximal average and extension to all l1 inputs

Defines the literal local average in Proposition 4.19 for every l1 input: the supremum over all real M>=N of M^-2 times the sum of |f(y)| over |x-y|<=M^2. Lean proves summability, positivity, boundedness of the supremum, and its l1 norm majorant. It proves that each finite dyadic local mass already used by the low-kernel analysis is dominated by this all-input source supremum, taking M=sqrt(2^j N^2). A general continuous convolution lemma then extends any existing finite-input dyadic local bound to the actual l1-to-l-infinity Fourier operator on all l1 inputs, using a proved convergent sum rather than a density assertion left informal. Thus the final local clause will use the printed source quantity with the absolute radius constant C=1. This is an unconditional supporting proof and adds no analytic input. The selected family, independent-input boundaries, completed prior results and manuscript remain unchanged.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| SourceLocalMass.lean | 9 |

- `sourceBall_summable`
- `sourceBallMass_nonneg`
- `sourceBallMass_uniform`
- `sourceLocalMass_bddAbove`
- `sourceBallMass_le_local`
- `sourceLocalMass_nonneg`
- `sourceLocalMass_uniform`
- `finiteDyadicLocalMass_le_source`
- `fourierL1Operator_local_of_finite`

<!-- checkpoint-verification -->

## Verification

All 853 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4460-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2204 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 855 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results under their paper hypotheses remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. In addition, Lemma 3.21 and BOTH conclusions of Theorem 1.1 are complete checked implications under their explicit independent deep inputs. The PNT limits are used in the sharp Gauss/high bound; an imported PNT bridge is not integrated. Both source clauses of Proposition 6.21 are also complete checked implications under their recorded independent inputs. The whole paper, Proposition 4.19 and the later headline applications remain unfinished. See docs/THEOREM_1_1_EXTERNAL_INPUTS.md. PNT limits, raw compatible progression/Ren/Ghosh data, and the global independent square decomposition remain explicit hypotheses. Reflection between plus and minus square translations is proved without any extra analytic assumption. The smooth multifrequency boundary is only for later maximal applications.

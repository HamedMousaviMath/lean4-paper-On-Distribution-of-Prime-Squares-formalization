# Checkpoint 759: Prove sharp maximal bounds for both actual high-block pieces

Both actual pieces of a dyadic high block now have sharp maximal majorants. The collar proof allows arbitrary changing upper denominator cutoffs by masking its coefficients and uses the already proved square-function estimate. The large-denominator proof uses the actual joint scale-and-cutoff maximum, not a scalar symbol norm. After extracting the common amplitude A sqrt(B) Q^(-1/2) exp(G(log Q)), both bounds have the same two-sided relative-cutoff profile; the large piece also has the verified cubic logarithmic factor. An effective cutoff at least 16 ensures that every nonempty large block satisfies the separation index required by the source theorem. Empty blocks and all smaller collar blocks are explicitly handled.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| SharpAnnularBlockMaximum.lean | 2 |

- `sharpCollar_block_maximum`
- `sharpLarge_block_maximum`

<!-- checkpoint-verification -->

## Verification

All 826 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4433-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2060 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 828 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results under their paper hypotheses remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. In addition, Lemma 3.21 and BOTH conclusions of Theorem 1.1 are complete checked implications under their explicit independent deep inputs. The PNT limits are used in the sharp Gauss/high bound; an imported PNT bridge is not integrated. The whole paper, the full maximal clauses of Proposition 4.19/6.21 and the later headline applications remain unfinished. See docs/THEOREM_1_1_EXTERNAL_INPUTS.md. PNT limits, raw compatible progression/Ren/Ghosh data, and the independent square decomposition remain explicit hypotheses. The smooth multifrequency boundary is only for later maximal applications.

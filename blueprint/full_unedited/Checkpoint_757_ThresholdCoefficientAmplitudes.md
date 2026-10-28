# Checkpoint 757: Extract sharp conductor-sensitive amplitudes on both sides of the cutoff

The common-threshold Gauss-product envelope now gives separate, exact coefficient bounds on both sides of an effective cutoff. After extracting A sqrt(B) Q^(-1/2) exp(G(log Q)), the small-denominator coefficient is bounded by t^(-1/2), and the large-denominator coefficient by t^(-1/4). These imply uniform amplitudes on each dyadic denominator block. Two elementary profile inequalities convert the actual collar gain and the large-block maximum into the same two-sided profile of exponent 1/4. The argument preserves the conductor factor rather than replacing it by a worse denominator estimate.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| ThresholdCoefficientAmplitudes.lean | 7 |

- `sharpThresholdAmplitude_nonneg`
- `threshold_coefficient_small`
- `threshold_coefficient_large`
- `threshold_small_block_amplitude`
- `threshold_large_block_amplitude`
- `large_amplitude_profile`
- `small_amplitude_profile`

<!-- checkpoint-verification -->

## Verification

All 824 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4431-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2053 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 826 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results under their paper hypotheses remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. In addition, Lemma 3.21 and BOTH conclusions of Theorem 1.1 are complete checked implications under their explicit independent deep inputs. The PNT limits are used in the sharp Gauss/high bound; an imported PNT bridge is not integrated. The whole paper, the full maximal clauses of Proposition 4.19/6.21 and the later headline applications remain unfinished. See docs/THEOREM_1_1_EXTERNAL_INPUTS.md. PNT limits, raw compatible progression/Ren/Ghosh data, and the independent square decomposition remain explicit hypotheses. The smooth multifrequency boundary is only for later maximal applications.

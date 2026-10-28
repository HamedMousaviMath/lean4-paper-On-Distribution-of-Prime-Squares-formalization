# Checkpoint 728: Sharp threshold envelopes on both sides of the denominator cutoff

Proves that the common-threshold slope tends to zero and is eventually at most one quarter. Under the existing two PNT inputs, the threshold exponent divided by the source regularized Orlicz weight tends to2, with its full epsilon consequence. The actual conductorRho product is bounded uniformly below the threshold and with a quarter-power relative loss above it. These are the arithmetic envelopes required for the fixed-scale high bound; no source high estimate or Theorem1.1 conclusion is assumed.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| ThresholdEnvelopeBounds.lean | 6 |

- `gaussThresholdSlope_tendsto_zero`
- `gaussThresholdSlope_eventually_quarter`
- `gaussAnalyticMajorant_regularized_ratio_tendsto`
- `gaussAnalyticMajorant_regularized_eventually`
- `conductorRho_threshold_small`
- `conductorRho_threshold_large`

<!-- checkpoint-verification -->

## Verification

All 795 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4402-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 1957 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 797 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. The raw progression-prefix and published Ren/Ghosh estimates remain explicit unproved hypotheses. SmoothCircleBourgainInput is a newly explicit compound unproved external analytic boundary, comprising the general smooth multifrequency estimate, sampling, normalization and fixed bump. Its existence is not proved. The Lean theorems prove implications conditional on it; the axiom audit does not certify this hypothesis. No own-paper annular lemma is assumed.

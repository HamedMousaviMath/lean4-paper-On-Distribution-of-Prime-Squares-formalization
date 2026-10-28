# Checkpoint 730: Threshold bounds for masked coefficients

Proves the threshold estimate for an actual complex coefficient multiplied by the annular high mask. The bound uses the geometric relative-cutoff profile with exponent one quarter, retaining the sharp Gauss envelope and the square root of the conductor scale. Includes both sides of the cutoff and the exact inverse-square-root rescaling identity. This is a supporting estimate; no main paper theorem is declared completed. No deep external input is used in this checkpoint.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| ThresholdMaskedCoefficientBounds.lean | 5 |

- `relativeCutoffProfile_small`
- `relativeCutoffProfile_large`
- `inverse_sqrt_relative`
- `conductorRho_scaled_threshold_large`
- `threshold_masked_product`

<!-- checkpoint-verification -->

## Verification

All 797 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4404-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 1966 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 799 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. The raw progression-prefix and published Ren/Ghosh estimates remain explicit unproved hypotheses. SmoothCircleBourgainInput is a newly explicit compound unproved external analytic boundary, comprising the general smooth multifrequency estimate, sampling, normalization and fixed bump. Its existence is not proved. The Lean theorems prove implications conditional on it; the axiom audit does not certify this hypothesis. No own-paper annular lemma is assumed.

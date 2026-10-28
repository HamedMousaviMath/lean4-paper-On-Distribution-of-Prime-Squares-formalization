# Checkpoint 721: The generic smooth input applies to the actual weighted source projection

Assuming the explicitly unproved generic smooth multifrequency input, applies it to the actual weighted circle source projection. The fixed weighted cutoff is applied to the input once. Periodic rational separation and the two large-start inequalities are proved and retained explicitly, and the bound has no coefficient cardinality loss. This is a conditional application, not a proof of the external input, the full all-scale source estimate, or Theorem 1.1.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| BourgainWeightedSourceProjection.lean | 1 |

- `bourgain_weightedSource_projection`

<!-- checkpoint-verification -->

## Verification

All 788 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4395-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 1940 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 790 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. The raw progression-prefix and published Ren/Ghosh estimates remain explicit unproved hypotheses. SmoothCircleBourgainInput is a newly explicit compound unproved external analytic boundary, comprising the general smooth multifrequency estimate, sampling, normalization and fixed bump. Its existence is not proved. The Lean theorems prove implications conditional on it; the axiom audit does not certify this hypothesis. No own-paper annular lemma is assumed.

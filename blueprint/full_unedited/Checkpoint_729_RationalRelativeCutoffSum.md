# Checkpoint 729: Uniform rational sums with two relative denominator cutoffs

Proves a denominator-relative cutoff profile and bounds a genuine finite rational-frequency sum by its dyadic profile, including all small dyadic scales. Reuses the already proved uniform interpolation-weight sum to obtain a two-cutoff bound independent of the ordinary and exceptional positive cutoff locations. This provides the geometric summation needed for the sharp fixed-scale high symbol; no multifrequency maximal input, PNT, or own-paper high estimate is assumed.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| RationalRelativeCutoffSum.lean | 4 |

- `relativeCutoffProfile_nonneg`
- `relativeCutoffProfile_dyadic`
- `rational_dyadic_profile_sum`
- `rational_two_relative_cutoff_sum`

<!-- checkpoint-verification -->

## Verification

All 796 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4403-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 1961 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 798 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. The raw progression-prefix and published Ren/Ghosh estimates remain explicit unproved hypotheses. SmoothCircleBourgainInput is a newly explicit compound unproved external analytic boundary, comprising the general smooth multifrequency estimate, sampling, normalization and fixed bump. Its existence is not proved. The Lean theorems prove implications conditional on it; the axiom audit does not certify this hypothesis. No own-paper annular lemma is assumed.

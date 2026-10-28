# Checkpoint 726: A general weighted annular block has a conditional large-start countable maximum

Defines the actual weighted bare annular source block with fixed rational centers and coefficients, proves its exact smooth-plus-error decomposition, and derives a genuine countable real-l2 majorant conditional on SmoothCircleBourgainInput C. The bound is A*(C*circleFrequencyLogFactor/2+E) times the input norm. Beta may vary with time in [0,1]. Both large-start inequalities and s>=2 remain explicit. No new external hypothesis is introduced. Arbitrary starting scales, small source scales, denominator/conductor summation and the printed stronger multifrequency claims remain open. The paper-level checklist is saved and its 54-claim coverage is refreshed with every subsequent checkpoint; this supporting unit closes no new whole paper statement.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| WeightedAnnularLargeStartMaximum.lean | 2 |

- `weightedAnnularSourceBlock_decomposition`
- `largeStart_weightedAnnular_maximum`

<!-- checkpoint-verification -->

## Verification

All 793 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4400-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 1946 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 795 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. The raw progression-prefix and published Ren/Ghosh estimates remain explicit unproved hypotheses. SmoothCircleBourgainInput is a newly explicit compound unproved external analytic boundary, comprising the general smooth multifrequency estimate, sampling, normalization and fixed bump. Its existence is not proved. The Lean theorems prove implications conditional on it; the axiom audit does not certify this hypothesis. No own-paper annular lemma is assumed.

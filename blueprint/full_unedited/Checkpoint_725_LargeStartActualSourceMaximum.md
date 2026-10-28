# Checkpoint 725: The original Gauss source block has a conditional large-start countable maximum

Combines the conditional smooth-main maximum with the fully proved annular projection-error maximum for the original source Gauss model. The resulting countable real-l2 majorant has bound (A0+A1)*(C*logFactor/2+E). Every support, scale, fixed-character, coefficient and beta hypothesis is displayed. This milestone is conditional on the generic external smooth multifrequency predicate; arbitrary starting scales, denominator/conductor summation, Proposition 6.21, Proposition 4.19 and Theorem 1.1 remain open.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| LargeStartActualSourceMaximum.lean | 1 |

- `largeStart_actualSource_maximum`

<!-- checkpoint-verification -->

## Verification

All 792 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4399-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 1944 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 794 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. The raw progression-prefix and published Ren/Ghosh estimates remain explicit unproved hypotheses. SmoothCircleBourgainInput is a newly explicit compound unproved external analytic boundary, comprising the general smooth multifrequency estimate, sampling, normalization and fixed bump. Its existence is not proved. The Lean theorems prove implications conditional on it; the axiom audit does not certify this hypothesis. No own-paper annular lemma is assumed.

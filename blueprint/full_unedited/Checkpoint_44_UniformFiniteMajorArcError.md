# Checkpoint 44: Uniform logarithmic major-arc approximation for the actual finite model

The actual finite model error now has the full major-arc logarithmic rate with a single threshold independent of Q, the finite set of canonical rational centers, the chosen major arc and the exceptional character data. For fixed C>=0, c>0 and A>=0, and the established source range for Q, the theorem concludes

\[\|\widehat A_N(\xi)-V_{N,\Gamma}(\xi)\|\le 2^A Q^{-1/2}(1+\log N)^{-A}.\]

The hypotheses are explicit: N sufficiently large; Q>=1 in its source range; canonical centers with denominator at most R(N,Q); coefficient norms at most one; beta in (0,1]; a chosen center in the finite set with the required major-arc width; and the actual von-Mangoldt progression-prefix estimate throughout the positive annulus with the same exceptional data. The proof joins the source parameter, geometric and error-budget thresholds, applies the checked prefix-to-model estimate, then absorbs the counted tail. No minor-arc estimate or existence of exceptional data is assumed implicitly. This is the major-arc branch for the finite real-frequency model; the source's global approximation is still open.


## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| UniformFiniteMajorArcError.lean | 1 |

- `finiteMajorArcError_uniform_log_rate`

<!-- checkpoint-verification -->

## Verification

All 111 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 3630-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 851 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 113 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. The already displayed raw progression-prefix estimate is consumed as a theorem hypothesis; it remains unproved. No new external analytic estimate or own-paper lemma is assumed.

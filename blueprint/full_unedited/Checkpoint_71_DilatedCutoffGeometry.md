# Checkpoint 71: Exact support and core widths for arithmetic narrow cutoffs

For every positive real dilation A, the actual smooth cutoff eta(A theta) has support inside |theta|<1/A and equals one when |theta|<=1/(2A). These exact width statements extend the already checked dyadic cutoff geometry to the arithmetic narrow-cutoff dilations qN^2/Q and B0(q/q0)N^2/Q used by the low model. Positivity of the dilation is explicit.


## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| DilatedCutoffGeometry.lean | 2 |

- `dilatedSourceCutoff_radius`
- `dilatedSourceCutoff_core`

<!-- checkpoint-verification -->

## Verification

All 138 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 3657-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 907 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 140 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. The already displayed raw progression-prefix estimate is consumed as a theorem hypothesis; it remains unproved. No new external analytic estimate or own-paper lemma is assumed.

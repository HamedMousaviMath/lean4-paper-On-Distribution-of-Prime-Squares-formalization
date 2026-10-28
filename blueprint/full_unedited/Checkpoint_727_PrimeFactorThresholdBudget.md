# Checkpoint 727: A common prime-factor threshold controls every conductor product

Proves an arbitrary fixed-threshold reciprocal prime-factor budget and the corresponding bound for the logarithm of the actual conductorRho product, uniformly for every positive modulus including small moduli. The resulting exponential envelope is centered at a common threshold y and has the explicit slope gaussThresholdSlope y. These elementary statements use no PNT input; PNT will later identify the sharp leading constant of the envelope at y=log Q. This is the first arithmetic step on the fixed-scale route to Theorem1.1, which does not require the full countable high maximum. No whole source statement is newly closed.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| PrimeFactorThresholdBudget.lean | 5 |

- `primeFactors_reciprocal_threshold`
- `gaussThresholdSlope_nonneg`
- `log_conductorRho_le`
- `conductorRho_log_threshold`
- `conductorRho_exp_threshold`

<!-- checkpoint-verification -->

## Verification

All 794 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4401-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 1951 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 796 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. The raw progression-prefix and published Ren/Ghosh estimates remain explicit unproved hypotheses. SmoothCircleBourgainInput is a newly explicit compound unproved external analytic boundary, comprising the general smooth multifrequency estimate, sampling, normalization and fixed bump. Its existence is not proved. The Lean theorems prove implications conditional on it; the axiom audit does not certify this hypothesis. No own-paper annular lemma is assumed.

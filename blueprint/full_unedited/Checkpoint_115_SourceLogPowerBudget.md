# Checkpoint 115: Uniform logarithmic absorption at the actual source scale

For the actual source scale R=max(exp((log N)^(1/10)),Q^8), Lean proves log R>=(log N)^(1/10). Hence, for N>=1 and every d>=0, (log N)^d<=(log R)^(10*d). All real-power compositions and the nonnegative logarithmic bases are justified.

Combining this with the preceding logarithmic absorption and the source scale's uniform lower growth gives one natural threshold, independent of Q, for

    (log(N/2))^d <= R^epsilon,

for every fixed d>=0 and epsilon>0. The statement quantifies over all real Q; no Q-dependent threshold is hidden. This handles Ren's fixed logarithmic loss at the exact annular scale.

The proof is unconditional and uses no PNT or prime exponential-sum hypothesis. It prepares the uniform error budget needed after the complementary geometric and analytic branches have been assembled.


## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| SourceLogPowerBudget.lean | 3 |

- `sourceMajorArcScale_log_lower`
- `source_log_power_domination`
- `source_annular_log_power_uniform`

<!-- checkpoint-verification -->

## Verification

All 182 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 3704-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 1025 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 184 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. Published Ren and Ghosh quadratic exponential-sum estimates, when consumed, remain displayed raw theorem hypotheses; the progression-prefix estimate also remains an explicit unproved input. No own-paper analytic conclusion is assumed.

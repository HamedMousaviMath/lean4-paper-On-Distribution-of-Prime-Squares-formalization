# Checkpoint 42: Uniform arithmetic thresholds for the major-arc model error

The finite major-arc budget is the actual sum of the prefix error and the tail from all other model terms:

\[B_C(R)=\frac{4+(2+4\pi)C}{R^5}+\left(5+\frac{\log R}{\log2}\right)\frac{4C_G}{\pi}R^{-5/12}.\]

The new proof gives a single natural-number threshold for every real Q. First the exponential part of R=max(exp((log N)^(1/10)),Q^8) tends to infinity independently of Q. This transfers the already proved eventual R^(-1/6) budget estimate uniformly to this scale. Joining this threshold with the proved logarithmic absorption gives, for every fixed C>=0 and A>=0, one N0 such that for all N>=N0 and all Q>=1,

\[B_C(R(N,Q))\le 2^A Q^{-1/2}(1+\log N)^{-A}.\]

The N0 may depend on C and A; it does not depend on Q. This is a genuine quantifier strengthening needed for the source approximation. No distribution theorem, minor-arc estimate or own-paper lemma is assumed by these three results. Applying this budget to the actual finite model still requires the major-arc hypotheses and the displayed raw progression-prefix estimate from checkpoint 41.


## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| UniformMajorArcBudget.lean | 3 |

- `sourceMajorArcScale_uniform_lower`
- `sourceMajorArcScale_uniform_model_budget`
- `sourceMajorArcScale_uniform_model_log_rate`

<!-- checkpoint-verification -->

## Verification

All 109 project modules and the root were freshly rebuilt: 3628 jobs pass without warnings/errors. All 848 named theorems pass the complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound. The source scan checks 111 Lean files. Exact unique import/audit coverage and unchanged frozen source hashes are checked before packaging. There are no placeholders or added mathematical axioms.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. The already displayed raw progression-prefix estimate is consumed as a theorem hypothesis; it remains unproved. No new external analytic estimate or own-paper lemma is assumed.

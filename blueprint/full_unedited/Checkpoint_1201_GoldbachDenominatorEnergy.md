# Checkpoint 1201: Actual rational-numerator count and added-denominator energy sum

The number of actual source rational centers of each denominator is proved exactly phi(q), including modulus1 and arbitrary denominator filters. No coarse center-count substitution is used in the energy sum.

After multiplying the actual squared local prefactor by phi(q), the denominator contribution is bounded by the fixed tau(q)^12/q² weight. The proved finite divisor tail therefore yields one absolute K such that the sum of squared local prefactors over every R<q≤Y is at most K(log N)^4/sqrt(R), uniformly in the real upper cutoff Y.

This is the complete arithmetic denominator-energy sum for the added source moduli; only the already-proved local analytic energy and disjoint Bessel inequality remain to be combined with it.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachDenominatorEnergy.lean | 4 |

- `goldbach_centers_denominator_sum`
- `goldbach_centers_filtered_denominator_sum`
- `goldbach_major_prefactor_count`
- `goldbach_added_denominator_energy_budget`

<!-- checkpoint-verification -->

## Verification

All 1268 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 5061-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 4033 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1270 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; the Section10/11 analytic and sieve estimates remain open internal obligations. The rational smooth multifrequency theorem with circle transference remains an explicit independent compound hypothesis. The classical primitive sum-of-two-squares criterion is an additional explicit independent arithmetic hypothesis for Section9 reductions; it contains no own-paper conclusion and is not declared as a Lean axiom.

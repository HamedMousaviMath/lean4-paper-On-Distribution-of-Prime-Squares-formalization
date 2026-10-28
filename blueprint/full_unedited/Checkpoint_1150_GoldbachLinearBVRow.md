# Checkpoint 1150: Actual ordinary-BV row approximation with independent prime cutoffs

The actual source linear major model and error are explicit functions. The sum of error norms over an arbitrary finite row of positive moduli is bounded by (1+q)card(K)+(1+2*pi)R³ times the ordinary unweighted modulus-distribution error sum. Each progression may have its own real cutoff W_k≥2 and its own coprime residue. Applying RawPrimeBombieriVinogradovInput gives one level, constant and starting scale chosen before q, all residue families and cutoffs. The remaining terms1+q are exactly the retained nonunit/strict-endpoint contribution, not an unproved distribution assumption. This completes the genuine BV row conversion. Matching the paper's source level and summing over ell are the next internal steps.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachLinearBVRow.lean | 2 |

- `goldbach_linear_error_sum_unweighted`
- `goldbach_linear_major_bv_row`

<!-- checkpoint-verification -->

## Verification

All 1217 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 5008-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 3788 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1219 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; the Section10/11 analytic and sieve estimates remain open internal obligations. The rational smooth multifrequency theorem with circle transference remains an explicit independent compound hypothesis. The classical primitive sum-of-two-squares criterion is an additional explicit independent arithmetic hypothesis for Section9 reductions; it contains no own-paper conclusion and is not declared as a Lean axiom.

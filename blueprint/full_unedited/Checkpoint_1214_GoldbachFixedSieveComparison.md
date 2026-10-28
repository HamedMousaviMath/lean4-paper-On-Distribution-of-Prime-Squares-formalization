# Checkpoint 1214: Section11 fixed sieve sets and exact exceptional count

Started Section11 with the actual fixed lower and upper prime sets. The lower comparison and the exact upper exceptional-pair inclusion are proved. Every lost upper pair is indexed by a prime p dividing n, has r=n-p^2, and has multiplier ell dividing n-p^2-1. Finite pair counting gives the complete exact upper comparison with error sum over p|n of tau(n-p^2-1). The actual closed multiplier set and its n-dependent subset are used. No deep input is added; the uniform power error is the next proof obligation.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachFixedSieveComparison.lean | 11 |

- `mem_goldbachSievePairs`
- `goldbachSievePairs_card`
- `goldbach_fixed_lower_subset`
- `goldbach_fixed_lower_values_subset`
- `goldbach_fixed_lower_count`
- `goldbach_fixed_upper_subset`
- `goldbach_fixed_upper_exception`
- `goldbach_fixed_sieve_exceptions_card`
- `goldbach_fixed_upper_count_finite`
- `goldbach_closed_multiplier_positive`
- `goldbach_fixed_upper_source_count_finite`

<!-- checkpoint-verification -->

## Verification

All 1281 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 5074-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 4084 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1283 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; all Section10 statements and the full circle-method implication are complete in the agreed conditional scope; Section11 remains open. The rational smooth multifrequency theorem with circle transference remains an explicit independent compound hypothesis. The classical primitive sum-of-two-squares criterion is an additional explicit independent arithmetic hypothesis for Section9 reductions; it contains no own-paper conclusion and is not declared as a Lean axiom.

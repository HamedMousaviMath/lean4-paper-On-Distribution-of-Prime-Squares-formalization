# Checkpoint 1122: Exact prime-progression row grouping and energy reduction

The literal progression polynomial is now regrouped by its positive integer ell and its actual prime t. Each row retains exactly the moduli present in the original finite index set I. The membership equivalence for the row modulus set and the general row-sum identity are proved, so this regrouping does not duplicate or drop arithmetic indices.

The complex row coefficient is the sum of the original d(k,ell) over exactly those row moduli satisfying the source residue condition. Its norm is bounded by the actual congruence multiplicity when every coefficient has norm at most one. The full continuous circle polynomial is proved equal to the regrouped prime-product polynomial, with the original W cutoff and ell*t<N^2 restriction intact.

Applying the checked prime-frequency multiplicity bound yields an actual integral inequality: the energy is at most log(N^2)/log 2 times the sum over ell and 1<=t<=N^2/ell of the squared row congruence multiplicity. The extension from the original primes/W-cutoff to this finite interval is proved by an explicit injection and nonnegative summation. Only positivity of the source ell indices and the normal coefficient bound are needed. No prime-distribution, PNT or sieve theorem is assumed.

These five supporting theorems complete the exact bridge between the efficient frequency argument and the original progression polynomial. The remaining summation uses the row-square estimate proved at1120 and the printed local modulus-count bound. Its source-range verification is still to be supplied before claiming the full progression-energy estimate. No new manuscript replacement is required.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachProgressionRows.lean | 5 |

- `mem_goldbachModuliAt`
- `goldbach_index_row_sum`
- `goldbach_progression_row_coefficient_norm`
- `goldbach_progression_polynomial_by_rows`
- `goldbach_progression_energy_by_row_squares`

<!-- checkpoint-verification -->

## Verification

All 1189 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4980-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 3659 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1191 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; the Section10/11 analytic and sieve estimates remain open internal obligations. The rational smooth multifrequency theorem with circle transference remains an explicit independent compound hypothesis. The classical primitive sum-of-two-squares criterion is an additional explicit independent arithmetic hypothesis for Section9 reductions; it contains no own-paper conclusion and is not declared as a Lean axiom.

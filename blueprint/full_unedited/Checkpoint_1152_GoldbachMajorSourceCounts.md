# Checkpoint 1152: Actual source row sums and coefficient-family cardinality bounds

The actual active row set lies in1..N², its reciprocal sum is bounded by the harmonic number, and the sum of X_ell=N²/ell is at most3N² log N. The number of active rows is bounded by max(L0,0), including empty and negative-cutoff cases. Exact row regrouping and Cauchy–Schwarz give card(I)²≤3N² max(L0,0) log N from the printed square-root row cutoffs. These are proved finite-count bounds for the actual coefficient family; they will absorb every retained prime endpoint/nonunit term with the source N^(-delta) margin.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachMajorSourceCounts.lean | 5 |

- `goldbach_source_row_subset`
- `goldbach_source_row_reciprocal`
- `goldbach_source_row_scale_sum`
- `goldbach_source_row_card`
- `goldbach_source_index_card_square`

<!-- checkpoint-verification -->

## Verification

All 1219 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 5010-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 3798 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1221 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; the Section10/11 analytic and sieve estimates remain open internal obligations. The rational smooth multifrequency theorem with circle transference remains an explicit independent compound hypothesis. The classical primitive sum-of-two-squares criterion is an additional explicit independent arithmetic hypothesis for Section9 reductions; it contains no own-paper conclusion and is not declared as a Lean axiom.

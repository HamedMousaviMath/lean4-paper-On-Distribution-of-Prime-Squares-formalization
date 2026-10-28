# Checkpoint 1218: Selected sieve remainder estimates and upper argument shift

The completed circle-method mean-square bound is transferred to every fixed finite selected subfamily of allowed arithmetic indices by explicit zero extension. Missing residues are extended by1 and verified coprime, while all missing coefficients are zero. The actual n-1 upper-sieve shift is proved on any positive subset of the source range, and on the full natural range with a factor2 that handles the extra zero-boundary term. Constants remain fixed before the selected family and coefficients. Only the existing raw SW, BV and Ren/Ghosh inputs are used; no general sieve input or own-paper endpoint is added.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachSieveRemainderTransport.lean | 3 |

- `goldbach_pred_square_sum_bound`
- `goldbach_pred_full_square_sum_bound`
- `goldbach_sieve_remainders_selected`

<!-- checkpoint-verification -->

## Verification

All 1285 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 5078-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 4105 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1287 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; all Section10 statements and the full circle-method implication are complete in the agreed conditional scope; Section11 remains open. The rational smooth multifrequency theorem with circle transference remains an explicit independent compound hypothesis. The classical primitive sum-of-two-squares criterion is an additional explicit independent arithmetic hypothesis for Section9 reductions; it contains no own-paper conclusion and is not declared as a Lean axiom.

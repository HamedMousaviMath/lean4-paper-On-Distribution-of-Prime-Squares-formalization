# Checkpoint 1137: Exact strict progression cutoff and the possible prime endpoint

The strict source cutoff ell*t<N² is retained. When W≤N²/ell, the actual progression cutoff equals the ordinary prime progression cutoff with the possible equality ell*t=N² removed. There is at most one such prime, and the corresponding actual complex exponential-sum difference has norm at most1. Replacing W by min(W,N²/ell) is proved to leave the strict source cutoff unchanged. This corrects the boundary bookkeeping required before partial summation: the manuscript sentence saying the strict condition is automatic under a non-strict bound is false at equality. No main theorem change is inferred; the finite endpoint term is explicit and still has to be included in the eventual major-arc bound. The source archive and selected manuscript are preserved unchanged.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachMajorStrictEndpoint.lean | 5 |

- `mem_goldbachPrimeProgressionCutoff`
- `goldbach_progression_strict_endpoint`
- `goldbach_progression_endpoint_card`
- `goldbach_progression_endpoint_error`
- `goldbach_progression_cutoff_min`

<!-- checkpoint-verification -->

## Verification

All 1204 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4995-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 3726 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1206 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; the Section10/11 analytic and sieve estimates remain open internal obligations. The rational smooth multifrequency theorem with circle transference remains an explicit independent compound hypothesis. The classical primitive sum-of-two-squares criterion is an additional explicit independent arithmetic hypothesis for Section9 reductions; it contains no own-paper conclusion and is not declared as a Lean axiom.

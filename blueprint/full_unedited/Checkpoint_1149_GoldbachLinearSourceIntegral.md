# Checkpoint 1149: Exact strict Euclidean source integral and numeric major-arc error

The actual strict Euclidean source integral J_{ell,W} is defined using2≤v≤W and ell*v<N². Its domain is proved almost everywhere equal to (2,min(W,N²/ell)], so the integral equals the actual closed logarithmic integral at the clamped endpoint. Both the prime cutoff and the integral are therefore matched exactly under clamping, including equality cases. The actual full linear progression model is proved for every real W≥2 whenever N²/ell≥2. On a source major arc its error is at most1+q+(1+2*pi)R² B. Every domain and boundary correction is retained explicitly; the strict source condition is never replaced by an automatic non-strict condition.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachLinearSourceIntegral.lean | 4 |

- `goldbach_linear_source_domain_ae`
- `goldbach_linear_source_integral`
- `goldbach_linear_source_major_from_counts`
- `goldbach_linear_source_major_numeric`

<!-- checkpoint-verification -->

## Verification

All 1216 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 5007-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 3786 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1218 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; the Section10/11 analytic and sieve estimates remain open internal obligations. The rational smooth multifrequency theorem with circle transference remains an explicit independent compound hypothesis. The classical primitive sum-of-two-squares criterion is an additional explicit independent arithmetic hypothesis for Section9 reductions; it contains no own-paper conclusion and is not declared as a Lean axiom.

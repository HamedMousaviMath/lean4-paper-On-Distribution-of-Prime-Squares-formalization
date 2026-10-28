# Checkpoint 1151: Printed source ranges imply the ordinary BV level uniformly

The source arithmetic scale X_ell=N²/ell is proved to satisfy N^delta<X_ell≤N² under the printed strict ell range. The exact logarithmic comparisons delta log N≤log X_ell≤2 log N follow. Taking B≥C+L+1 and log N≥2^L puts V_ell R below the classical BV level sqrt(X_ell)(log X_ell)^(-L). The logarithmic saving at X_ell is converted to the saving at N with explicit factor delta^(-T). One natural threshold, independent of ell and the major denominator, is proved to ensure the required starting-scale and logarithmic inequalities. The lcm moduli then lie in the BV range. No source range is strengthened silently.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachBVSourceParameters.lean | 5 |

- `goldbach_progression_scale_logs`
- `goldbach_bv_log_level`
- `goldbach_bv_log_saving`
- `goldbach_bv_source_eventual_threshold`
- `goldbach_lcm_bv_level`

<!-- checkpoint-verification -->

## Verification

All 1218 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 5009-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 3793 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1220 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; the Section10/11 analytic and sieve estimates remain open internal obligations. The rational smooth multifrequency theorem with circle transference remains an explicit independent compound hypothesis. The classical primitive sum-of-two-squares criterion is an additional explicit independent arithmetic hypothesis for Section9 reductions; it contains no own-paper conclusion and is not declared as a Lean axiom.

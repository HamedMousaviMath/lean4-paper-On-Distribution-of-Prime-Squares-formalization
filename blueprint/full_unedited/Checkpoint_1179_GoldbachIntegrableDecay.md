# Checkpoint 1179: Two-sided Euclidean integrability and quantitative tail assembly

A strongly measurable complex function with a uniform bound M on |gamma|≤c and decay B|gamma|^(-3/2) outside that interval is proved integrable on the entire real line. Its actual L1 norm is at most2Mc+4B/sqrt(c). The proof evaluates both improper tails, controls the finite interval and proves the negative-half-line change of variables.

This general fact supplies the missing analytic justification for applying Fourier inversion to the genuine Euclidean product and for bounding smoothing errors. It has no unproved analytic input. The singular-integral and major-completion source statements remain open until their actual functions are substituted and the final comparisons are proved.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachIntegrableDecay.lean | 2 |

- `goldbach_halfline_integrable_decay`
- `goldbach_two_sided_integrable_decay`

<!-- checkpoint-verification -->

## Verification

All 1246 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 5039-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 3941 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1248 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; the Section10/11 analytic and sieve estimates remain open internal obligations. The rational smooth multifrequency theorem with circle transference remains an explicit independent compound hypothesis. The classical primitive sum-of-two-squares criterion is an additional explicit independent arithmetic hypothesis for Section9 reductions; it contains no own-paper conclusion and is not declared as a Lean axiom.

# Checkpoint 1146: Full uniform SW square major-arc approximation from ordinary prime counts

The full actual square major approximation is now proved from the ordinary unweighted SW interface. For every t>0 and C≥0, a positive constant and one natural threshold work simultaneously for all positive q≤(log N)^C, all integer numerators, every real2≤U≤N and every |gamma|≤(log N)^C/N². The model is exactly s(-a,q) I_U(gamma), with the actual logarithmic integral. The error is at most K N(log N)^(-t). Every prime cutoff, rational sign, residue normalization, nonunit term and eventual power absorption is proved. No large-U-only restriction or weighted square approximation is an assumption. The classical ordinary SW theorem remains the explicit independent unproved input.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachSquareMajorSW.lean | 1 |

- `goldbach_square_major_siegel_walfisz`

<!-- checkpoint-verification -->

## Verification

All 1213 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 5004-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 3772 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1215 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; the Section10/11 analytic and sieve estimates remain open internal obligations. The rational smooth multifrequency theorem with circle transference remains an explicit independent compound hypothesis. The classical primitive sum-of-two-squares criterion is an additional explicit independent arithmetic hypothesis for Section9 reductions; it contains no own-paper conclusion and is not declared as a Lean axiom.

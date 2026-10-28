# Checkpoint 1148: Actual linear Upsilon model with every nonunit and endpoint error

The actual good linear prime sum is approximated by the exact source Upsilon coefficient times the logarithmic integral, with error at most q B(1+2*pi*|ell*gamma| W) from ordinary prime-count discrepancies for the lcm modulus. All compatible classes are present. Primes nonunit modulo lcm(k,q) are proved to divide q using the source coprime residue condition, and their total norm is at most q. The strict source endpoint contributes at most1. Thus the actual full progression polynomial has the source model with the explicit error1+q+q B(1+2*pi*|ell*gamma| W). No omitted exceptional prime or equality endpoint is hidden in a distribution assumption.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachLinearMajorCounts.lean | 5 |

- `goldbach_good_linear_model_error`
- `goldbach_linear_nonunit_card`
- `goldbach_linear_nonunit_error`
- `goldbach_closed_linear_fourier`
- `goldbach_linear_major_from_counts`

<!-- checkpoint-verification -->

## Verification

All 1215 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 5006-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 3782 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1217 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; the Section10/11 analytic and sieve estimates remain open internal obligations. The rational smooth multifrequency theorem with circle transference remains an explicit independent compound hypothesis. The classical primitive sum-of-two-squares criterion is an additional explicit independent arithmetic hypothesis for Section9 reductions; it contains no own-paper conclusion and is not declared as a Lean axiom.

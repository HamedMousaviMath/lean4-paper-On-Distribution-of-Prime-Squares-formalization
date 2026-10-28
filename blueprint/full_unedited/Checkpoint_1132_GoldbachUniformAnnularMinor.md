# Checkpoint 1132: Actual prime partial sums from raw annular Ren-Ghosh inputs

The common annular bound at all relevant smaller scales is derived from the already recorded raw Ren/Ghosh input. It uses the proved rescaling of the actual source minor arcs. The assumptions are explicit elementary inequalities on a common cutoff H and radius R; in particular R⁴ ≤ H/2 and 1 ≤ R(H/N)². The strong-induction halving identity reconstructs all von Mangoldt partial sums. Finite Abel summation then removes the logarithmic prime weight, and the proved proper-prime-power mass bound accounts for the nonprime terms. The result bounds the actual unweighted prime-square polynomial for every real 0 ≤ U ≤ N. The only independent analytic assumption remains UniformRenGhoshInputs. The paper's own pointwise prime estimate is not assumed.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachUniformAnnularMinor.lean | 3 |

- `goldbachPrimeExponentialConstant_nonneg`
- `goldbach_common_annular_minor`
- `goldbach_prime_minor_from_numeric_parameters`

<!-- checkpoint-verification -->

## Verification

All 1199 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4990-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 3708 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1201 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; the Section10/11 analytic and sieve estimates remain open internal obligations. The rational smooth multifrequency theorem with circle transference remains an explicit independent compound hypothesis. The classical primitive sum-of-two-squares criterion is an additional explicit independent arithmetic hypothesis for Section9 reductions; it contains no own-paper conclusion and is not declared as a Lean axiom.

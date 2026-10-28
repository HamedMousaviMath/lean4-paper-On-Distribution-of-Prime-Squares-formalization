# Checkpoint 1200: Finite divisor-power denominator square tail

The finite inverse-three-halves tail is proved directly by integral comparison, including arbitrary finite subsets and real lower cutoffs R≥2. Its bound is4/sqrt(R), with the floor and endpoint conventions checked explicitly.

Combining that with the already-proved elementary divisor growth gives one positive absolute constant K such that sum_(q in S) tau(q)^12/q²≤K/sqrt(R) whenever every q in the finite set S exceeds R. The proof retains the full divisor power12 and has no smoothness restriction or upper denominator bound.

This is the denominator summation needed after counting the primitive numerators in the actual disjoint major-family energy estimate.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachDivisorSquareTail.lean | 3 |

- `goldbach_inverse_three_halves_interval`
- `goldbach_inverse_three_halves_tail`
- `goldbach_divisor_square_tail`

<!-- checkpoint-verification -->

## Verification

All 1267 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 5060-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 4029 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1269 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; the Section10/11 analytic and sieve estimates remain open internal obligations. The rational smooth multifrequency theorem with circle transference remains an explicit independent compound hypothesis. The classical primitive sum-of-two-squares criterion is an additional explicit independent arithmetic hypothesis for Section9 reductions; it contains no own-paper conclusion and is not declared as a Lean axiom.

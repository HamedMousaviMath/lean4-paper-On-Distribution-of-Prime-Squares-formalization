# Checkpoint 1142: Fixed-denominator lcm fibres and reduction to ordinary BV

For every fixed major denominator q, a fibre of k↦lcm(k,q)=h has cardinality at most q. The injection is k↦h/k; its values lie in1..q and determine k exactly. Consequently the sum of unweighted distribution errors over k is at most q times the ordinary sum over moduli h. If q≤R and each progression error is at most R² times the error for its lcm modulus, the total is at most R³ times the ordinary unweighted distribution-error sum. This proves an efficient route from classical unweighted BV to the actual progression approximation: all losses depending on q are powers of R=(log N)^C and can be absorbed in the requested logarithmic saving. No divisor-weighted BV theorem or divisor-moment input is needed for this route.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachMajorLCMQFibres.lean | 4 |

- `goldbach_lcm_quotient_range`
- `goldbach_lcm_fibre_card_le_q`
- `goldbach_lcm_unweighted_sum`
- `goldbach_major_error_from_unweighted_distribution`

<!-- checkpoint-verification -->

## Verification

All 1209 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 5000-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 3756 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1211 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; the Section10/11 analytic and sieve estimates remain open internal obligations. The rational smooth multifrequency theorem with circle transference remains an explicit independent compound hypothesis. The classical primitive sum-of-two-squares criterion is an additional explicit independent arithmetic hypothesis for Section9 reductions; it contains no own-paper conclusion and is not declared as a Lean axiom.

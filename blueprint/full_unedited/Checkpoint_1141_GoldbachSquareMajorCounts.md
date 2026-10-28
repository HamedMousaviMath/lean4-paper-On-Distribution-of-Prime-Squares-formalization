# Checkpoint 1141: Exact square major-arc model and its prime-count discrepancy bound

The actual positive prime-square polynomial is identified with the previously proved finite square symbol under the exact phase reflection. Actual prime progression cutoffs agree with residue fibres modulo q. The exceptional nonunit primes are bounded unconditionally by q. The existing finite Gauss assembly then gives the literal source square major-arc model s(-a,q) I_U(gamma), with error at most q+phi(q) B(1+4*pi*|gamma|*U²) when the ordinary reduced prime-count discrepancies up to U are at most B. Both the sign and the totient factor are proved, and the nonunit remainder is retained explicitly. A raw Siegel–Walfisz theorem will supply the ordinary counting discrepancy; the own square approximation is not an external input.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachSquareMajorCounts.lean | 6 |

- `goldbach_prime_positive_symbol`
- `goldbach_prime_residue_cutoff`
- `goldbach_square_prime_residue_sum`
- `goldbach_prime_nonunit_card`
- `goldbach_prime_nonunit_symbol`
- `goldbach_square_major_from_counts`

<!-- checkpoint-verification -->

## Verification

All 1208 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4999-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 3752 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1210 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; the Section10/11 analytic and sieve estimates remain open internal obligations. The rational smooth multifrequency theorem with circle transference remains an explicit independent compound hypothesis. The classical primitive sum-of-two-squares criterion is an additional explicit independent arithmetic hypothesis for Section9 reductions; it contains no own-paper conclusion and is not declared as a Lean axiom.

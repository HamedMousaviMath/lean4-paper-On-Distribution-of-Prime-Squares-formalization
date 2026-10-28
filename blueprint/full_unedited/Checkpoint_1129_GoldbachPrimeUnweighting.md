# Checkpoint 1129: Actual prime logarithmic unweighting and proper-prime-power error

The weighted-to-unweighted prime bridge is now proved for the literal Goldbach polynomial. Genuine Mangoldt partial sums and their logarithmically unweighted sums are defined with exact finite endpoints. Applying the finite Abel inequality at1128 gives norm at most B/log2 when all Mangoldt partial sums have norm at most B. The zero and one coefficients are handled explicitly.

For every prime p, logarithmic removal turns the actual von-Mangoldt coefficient into exactly one. The remainder is exactly the sum over nonprimes. Its norm is bounded using the already proved elementary proper-prime-power mass estimate; no PNT or distribution input is added. For every M<=N with N>=1, the comparison error is at most (2/log2)sqrt(N)log N.

The real endpoint convention is proved through the actual natural floor, including endpoints at primes. The terminal theorem gives, for every 0<=U<=N and every circle frequency, |P_U| <= B/log2+(2/log2)sqrt(N)log N from a uniform bound B on the genuine Mangoldt partial sums up to N. The eight supporting theorems prove the complete logarithmic-unweighting and prime-power-removal step rather than assuming it.

It remains to construct the uniform Mangoldt partial-sum bound from the existing raw annular Ren/Ghosh input on the actual complementary arcs. The halving argument, arc rescaling and logarithmic parameter choice are the next internal steps. The full source hybrid minor estimate is not yet claimed complete. No new independent deep assumption or manuscript replacement is introduced.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachPrimeUnweighting.lean | 8 |

- `goldbach_sum_range_succ_eq_Ioc`
- `goldbachMangoldtPrefix_Ioc`
- `goldbach_log_removed_mangoldt_bound`
- `goldbach_log_removed_prime_term`
- `goldbach_log_removed_mangoldt_split`
- `goldbach_prime_power_log_removal_error`
- `goldbachPrimeSquarePolynomial_floor`
- `goldbach_prime_from_mangoldt_partials`

<!-- checkpoint-verification -->

## Verification

All 1196 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4987-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 3693 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1198 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; the Section10/11 analytic and sieve estimates remain open internal obligations. The rational smooth multifrequency theorem with circle transference remains an explicit independent compound hypothesis. The classical primitive sum-of-two-squares criterion is an additional explicit independent arithmetic hypothesis for Section9 reductions; it contains no own-paper conclusion and is not declared as a Lean axiom.

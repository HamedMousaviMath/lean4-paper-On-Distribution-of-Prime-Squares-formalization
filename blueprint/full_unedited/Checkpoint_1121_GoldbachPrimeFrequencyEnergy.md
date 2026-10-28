# Checkpoint 1121: Prime-product frequency multiplicity and direct energy bound

A direct repeated-frequency energy principle is now proved. A finite exponential polynomial is regrouped exactly by its integer frequencies. Orthogonality and the already proved finite weighted square inequality give integral |sum c_i e(f_i theta)|^2 <= B sum |c_i|^2 whenever every frequency has at most B preimages. Repeated frequencies are counted, not silently treated as orthogonal.

For any finite set of pairs (ell,p) with positive ell and prime p, the fibre ell*p=m injects into the actual prime-divisor set of m by projection to p. Its cardinality is bounded by omega(m), independently of the coefficients. The elementary prime-product logarithmic budget already proved in the project yields omega(m)<=log X/log 2 whenever 0<m<=X. No PNT or distribution input is used.

Combining these statements gives a checked global energy bound for arbitrary complex coefficients indexed by positive ell and primes, with the factor log X/log 2 and the literal coefficient square sum. The seven new supporting theorems contain no new independent deep input. This alternative route can bypass the source dyadic off-diagonal bookkeeping once the arithmetic moduli are grouped correctly. That grouping and the final summation remain to be proved; no full progression-energy, hybrid or major-arc source claim is closed here. No manuscript replacement is required.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachPrimeFrequencyEnergy.lean | 7 |

- `goldbach_frequency_polynomial_regroup`
- `goldbach_distinct_frequency_energy`
- `goldbach_finite_sum_square`
- `goldbach_frequency_energy_multiplicity`
- `goldbach_prime_factor_count_log`
- `goldbach_prime_product_fibre_card`
- `goldbach_prime_product_energy`

<!-- checkpoint-verification -->

## Verification

All 1188 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4979-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 3654 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1190 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; the Section10/11 analytic and sieve estimates remain open internal obligations. The rational smooth multifrequency theorem with circle transference remains an explicit independent compound hypothesis. The classical primitive sum-of-two-squares criterion is an additional explicit independent arithmetic hypothesis for Section9 reductions; it contains no own-paper conclusion and is not declared as a Lean axiom.

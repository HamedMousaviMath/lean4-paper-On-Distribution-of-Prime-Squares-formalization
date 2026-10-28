# Checkpoint 1168: All prime-power coefficients and explicit two-adic bounds

The exact Upsilon normalization phi(gcd(q,k))/phi(q) is proved from the totient lcm identity. Direct finite norm estimates yield norm Upsilon≤phi(gcd(q,k)) and norm G_q≤q². These coarse bounds are used only to control the finite two-adic cases, not claimed as the required general Upsilon decay.

For every prime p and positive exponent a, the actual source coefficient satisfies norm G_{p^a}(ell,k,n)≤512 gcd(p^a,k*ell)/p^a. At odd primes, only a=1 contributes, by the earlier proved higher-power vanishing. At2, exponents at most3 use the explicit q² estimate; exponents at least4 vanish. Thus the two-adic contribution is fully controlled with an absolute constant. General-modulus decay is the next multiplicative deduction; Upsilon decay and actual smoothing/completion remain open.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachPrimePowerBounds.lean | 6 |

- `goldbach_upsilon_gcd_normalization`
- `goldbach_progression_exponential_trivial`
- `goldbach_upsilon_trivial_gcd`
- `goldbach_general_coefficient_trivial`
- `goldbach_general_coefficient_small_two_power`
- `goldbach_general_coefficient_prime_power`

<!-- checkpoint-verification -->

## Verification

All 1235 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 5028-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 3885 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1237 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; the Section10/11 analytic and sieve estimates remain open internal obligations. The rational smooth multifrequency theorem with circle transference remains an explicit independent compound hypothesis. The classical primitive sum-of-two-squares criterion is an additional explicit independent arithmetic hypothesis for Section9 reductions; it contains no own-paper conclusion and is not declared as a Lean axiom.

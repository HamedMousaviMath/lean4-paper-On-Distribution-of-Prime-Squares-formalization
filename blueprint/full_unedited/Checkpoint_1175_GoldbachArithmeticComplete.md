# Checkpoint 1175: Full arithmetic coefficient lemma and Euler product

Every clause of l:arithmeticcoefficients9 is now proved for the genuine source coefficients. The integer residue b is reduced to its canonical coprime representative; the Upsilon bound holds for arbitrary integer coprime b. The Gauss, Upsilon and G_q estimates share the absolute exponent C_1=9. Their constants can be chosen1, and the harmonic-family constant is9 exp(2).

The infinite local Euler factors are evaluated directly: all odd prime exponents beyond1 vanish, and the two-adic sum consists exactly of the exponents1,2,3. The full R-smooth series is absolutely summable and equals both the printed all-prime Euler product and the source arithmetic factor G_R. The statements hold for every R≥2, hence for the eventual logarithmic R in Section10. The harmonic theorem retains all strict real family cutoffs, every B≥0, and all positive arithmetic indices.

A clause-by-clause source review closes l:arithmeticcoefficients9 as proved. Positivity and smoothing of the actual singular integral, the full major completion and the final circle-method lemma remain internal obligations. No endpoint from this paper has become an external assumption. The selected manuscript is unchanged.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachArithmeticComplete.lean | 9 |

- `goldbach_upsilon_canonical_residue`
- `goldbach_upsilon_integer_gcd_decay`
- `goldbach_divisor_card_one_le`
- `goldbach_arithmetic_uniform_bounds`
- `goldbach_arithmetic_harmonic_common_exponent`
- `goldbach_odd_prime_power_series`
- `goldbach_two_prime_power_series`
- `goldbach_all_primes_euler_series`
- `goldbach_arithmetic_euler_complete`

<!-- checkpoint-verification -->

## Verification

All 1242 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 5035-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 3918 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1244 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; the Section10/11 analytic and sieve estimates remain open internal obligations. The rational smooth multifrequency theorem with circle transference remains an explicit independent compound hypothesis. The classical primitive sum-of-two-squares criterion is an additional explicit independent arithmetic hypothesis for Section9 reductions; it contains no own-paper conclusion and is not declared as a Lean axiom.

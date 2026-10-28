# Checkpoint 1169: General-modulus arithmetic and Gauss divisor decay

The genuine arithmetic coefficient is bounded at every positive modulus by tau(q)^9 gcd(q,k*ell)/q, uniformly in the source parameters. Its exact multiplicative factorization is combined with the proved prime-power estimates. The gcd ratio gcd(q,c)/q is itself factored by a proved coprime product identity. The elementary inequality2^omega(q)≤tau(q) turns the finite prime-factor weight512^omega(q) into tau(q)^9.

The actual principal square Gauss coefficient also satisfies norm s(a,q)≤tau(q)^3/sqrt(q) at every unit frequency, by the earlier unconditional twisted Gauss estimate and the same divisor comparison. No character bound, Gauss estimate or general-modulus coefficient decay is assumed as an external input. The remaining arithmetic clause in l:arithmeticcoefficients9 is the sharper individual Upsilon decay. The Euler identity, absolute convergence, full G_q decay, Gauss decay and source harmonic sum are now proved; full smoothing/completion and l:circmethod remain open.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachArithmeticDecay.lean | 7 |

- `goldbach_gcd_ratio_multiplicative`
- `goldbach_gcd_ratio_factorization`
- `goldbach_two_pow_primeFactors_le_divisors`
- `goldbach_prime_factor_weight_le_divisors`
- `goldbach_general_coefficient_factor_bound`
- `goldbach_general_coefficient_divisor_bound`
- `goldbach_principal_square_divisor_bound`

<!-- checkpoint-verification -->

## Verification

All 1236 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 5029-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 3892 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1238 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; the Section10/11 analytic and sieve estimates remain open internal obligations. The rational smooth multifrequency theorem with circle transference remains an explicit independent compound hypothesis. The classical primitive sum-of-two-squares criterion is an additional explicit independent arithmetic hypothesis for Section9 reductions; it contains no own-paper conclusion and is not declared as a Lean axiom.

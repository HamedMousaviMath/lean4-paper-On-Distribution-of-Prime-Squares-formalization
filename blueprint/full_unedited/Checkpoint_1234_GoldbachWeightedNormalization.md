# Checkpoint 1234: Exact lower and upper weighted Euler normalizations

Both arithmetic normalizations in the weighted comparison are now exact Lean identities for the original quantities. The lower identity is X_n*Theta_n(z)=3*C_R(n)*Re(H_(1,R)(n))*V_3(R,z), where V_3 is the literal product over R<p<z, p=3 mod4. For ell=2*u*p2, the upper identity is X_n(ell)*Theta_(n,ell)(z_ell)=6*B_R(n)*h_R(u)*Re(H_(ell,R)(n-1))/ell*V_all(R,z_ell). The explicit conditions are R>=3, R<z_ell, 0<u<z_ell<=p2, prime p2 and prime support of u in1 mod4. The actual closed multiplier geometry supplies these conditions once R< N^(2/9).

The proofs partition the actual finite prime sets at the inclusive small-prime cutoff, prove the small divisor equivalence p|ell iff p|u below p2, handle zero arithmetic factors without dividing by them, prove the prime-divisor product identity for h_R(u), and cancel the omitted outer factors exactly. The constants3 and6 are the exact24/phi(24) and24/phi(12), respectively. No asymptotic normalization is assumed. No new external input is used by these identities. The full weighted comparison remains open pending analytic summation, integration and smoothing.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachWeightedNormalization.lean | 14 |

- `mem_goldbach_weighted_outer_primes`
- `goldbach_weighted_outer_product_positive`
- `goldbach_weighted_small_divisors`
- `goldbach_weighted_upper_small_product`
- `goldbach_weighted_lower_prime_partition`
- `goldbach_weighted_lower_theta_partition`
- `goldbach_weighted_lower_normalization`
- `goldbach_weighted_prime_coprime_twelve`
- `goldbach_weighted_upper_prime_partition`
- `goldbach_weighted_upper_theta_partition`
- `goldbach_weighted_divisor_product`
- `goldbach_weighted_upper_outer_product`
- `goldbach_weighted_upper_arithmetic_normalization`
- `goldbach_weighted_upper_normalization`

<!-- checkpoint-verification -->

## Verification

All 1320 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 5113-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 4305 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1322 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; all Section10 statements and the full circle-method implication are complete in the agreed conditional scope; Section11 remains open. The effective Wirsing and prime Mertens inputs remain as recorded; this checkpoint proves exact arithmetic identities without consuming those inputs. The full Section11 lower-sieve proposition p:sieveneedlower8 is a complete conditional implication, including its actual main term, uniform o(1), n-independent coefficients and mean-square error. The uniform main-term lower bound l:maintermsize8 and its joint application with the same large cutoff C are also complete conditionally. The weighted upper main-term sum, upper sieve, numerical comparison and final Goldbach conclusion remain open.

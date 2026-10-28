# Checkpoint 1174: Actual Upsilon gcd decay from primitive frequency reduction

The primitive progression norm bound is proved for every divisor/complement pair, including the exact zero branch. This gives norm Upsilon(q,k,b,alpha)≤gcd(q,k)/phi(q) at every primitive additive frequency and source coprime residue.

The nonprimitive frequency is reduced exactly by d=gcd(q,ell). The quotient frequency is proved primitive, the reciprocal totient is bounded by tau(q)/q, divisor-cardinality monotonicity is checked, and the gcd contribution is transported through the common factor. The actual source coefficient satisfies norm Upsilon(alpha*ell,q,b,k)≤tau(q) gcd(q,k*ell)/q, stronger than the unspecified divisor-power estimate in the paper. No independent Lacey progression estimate or other new input is assumed. Integer residue transport and the common-exponent source arithmetic assembly are next.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachUpsilonDecay.lean | 5 |

- `goldbach_upsilon_int_modulus_congr`
- `goldbach_progression_exponential_primitive_norm`
- `goldbach_upsilon_primitive_decay`
- `goldbach_reciprocal_totient_divisor_bound`
- `goldbach_upsilon_gcd_divisor_decay`

<!-- checkpoint-verification -->

## Verification

All 1241 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 5034-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 3909 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1243 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; the Section10/11 analytic and sieve estimates remain open internal obligations. The rational smooth multifrequency theorem with circle transference remains an explicit independent compound hypothesis. The classical primitive sum-of-two-squares criterion is an additional explicit independent arithmetic hypothesis for Section9 reductions; it contains no own-paper conclusion and is not declared as a Lean axiom.

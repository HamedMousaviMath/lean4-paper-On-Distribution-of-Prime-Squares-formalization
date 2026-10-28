# Checkpoint 1164: Unconditional reciprocal-totient harmonic bounds

The reciprocal totient is bounded by the earlier actual conductor-correlation product divided by n. Its previously proved weighted harmonic estimate gives sum_{n≤D}1/phi(n)≤exp(2) H_D without an external average-totient input.

For every positive divisor d, the sum restricted to d|n is bounded by exp(2) H_D/phi(d). The proof uses the injective quotient n↦n/d and the proved supermultiplicativity phi(d)phi(n/d)≤phi(n). The actual gcd is expanded exactly as the sum of phi(d) over common divisors. These are unconditional arithmetic prerequisites for the source family harmonic estimate; the quantitative coefficient bounds and full major completion remain open.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachTotientHarmonic.lean | 4 |

- `goldbach_reciprocal_totient_majorant`
- `goldbach_reciprocal_totient_sum`
- `goldbach_reciprocal_totient_multiples`
- `goldbach_gcd_totient_divisor_expansion`

<!-- checkpoint-verification -->

## Verification

All 1231 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 5024-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 3862 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1233 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; the Section10/11 analytic and sieve estimates remain open internal obligations. The rational smooth multifrequency theorem with circle transference remains an explicit independent compound hypothesis. The classical primitive sum-of-two-squares criterion is an additional explicit independent arithmetic hypothesis for Section9 reductions; it contains no own-paper conclusion and is not declared as a Lean axiom.

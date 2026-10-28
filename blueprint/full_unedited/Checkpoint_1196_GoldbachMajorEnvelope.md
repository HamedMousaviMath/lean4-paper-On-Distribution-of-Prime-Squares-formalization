# Checkpoint 1196: Uniform Euclidean major-envelope square energy

A single nonnegative measurable Euclidean envelope is constructed from the actual flat and inverse-three-halves decay bounds. It is proved integrable with mass O(N), and its squared integral is proved O(N^4). The L2 estimate follows from its actual uniform O(N^3) bound and the proved L1 mass.

For every positive ell and all source U,W, the genuine product ell|I_U J_(ell,W)| is bounded by this common envelope. The empty progression-domain branch is explicitly included. A general domination theorem then gives the exact L2 energy bound for any strongly measurable local integrand controlled by the envelope.

This supplies the quantitative analytic factor for the disjoint added-modulus estimate. The remaining steps are the actual local arithmetic coefficients, denominator summation and the final major-model identities.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachMajorEnvelope.lean | 9 |

- `goldbach_major_envelope_nonnegative`
- `goldbach_major_envelope_bound`
- `goldbach_major_envelope_decay`
- `goldbach_major_envelope_measurable`
- `goldbach_major_envelope_integrable`
- `goldbach_major_envelope_energy`
- `goldbach_major_envelope_dominated_energy`
- `goldbach_linear_source_integral_empty`
- `goldbach_euclidean_product_envelope`

<!-- checkpoint-verification -->

## Verification

All 1263 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 5056-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 4011 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1265 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; the Section10/11 analytic and sieve estimates remain open internal obligations. The rational smooth multifrequency theorem with circle transference remains an explicit independent compound hypothesis. The classical primitive sum-of-two-squares criterion is an additional explicit independent arithmetic hypothesis for Section9 reductions; it contains no own-paper conclusion and is not declared as a Lean axiom.

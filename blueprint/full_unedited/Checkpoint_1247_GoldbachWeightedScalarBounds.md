# Checkpoint 1247: Weighted upper main term: uniform cutoffs and scalar errors

# Weighted upper main term: error absorption and valid cutoffs

The finite-kernel prime errors and Abel boundaries have explicit scalar majorants with the correct vanishing scale. The leading scalar identity preserves the exact W coefficient.

For R=(log N)^C and a=exp(sqrt(log N)), all hypotheses of the effective mean estimate are eventually valid: the lower scale, the prime-balance budget, the epsilon range, and the overlap with the coarse mean bound. These statements choose thresholds independently of n.

The small-denominator harmonic sum is bounded by (C_R/B_R) times a fixed constant times (log R)^6 plus the coarse mean tail. This retains all arithmetic dependence explicitly. The final weighted source comparison remains open until the uniform kernel and singular-integral assembly are complete.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachWeightedScalarBounds.lean | 4 |
| GoldbachWeightedCutoffBudgets.lean | 1 |
| GoldbachWeightedHarmonicCutoff.lean | 1 |

- `goldbach_weighted_prime_reciprocal_coarse`
- `goldbach_weighted_small_scalar`
- `goldbach_weighted_sharp_scalar_identity`
- `goldbach_weighted_large_scalar`
- `goldbach_weighted_cutoffs_eventually`
- `goldbach_weighted_harmonic_cutoff`

<!-- checkpoint-verification -->

## Verification

All 1348 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 5141-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 4405 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1350 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; all Section10 statements and the full circle-method implication are complete in the agreed conditional scope; Section11 remains open. Previously documented independent mean-value/Mertens inputs only. The full Section11 lower-sieve proposition p:sieveneedlower8 is a complete conditional implication, including its actual main term, uniform o(1), n-independent coefficients and mean-square error. The uniform main-term lower bound l:maintermsize8 and its joint application with the same large cutoff C are also complete conditionally. The weighted upper main-term sum, upper sieve, numerical comparison and final Goldbach conclusion remain open.

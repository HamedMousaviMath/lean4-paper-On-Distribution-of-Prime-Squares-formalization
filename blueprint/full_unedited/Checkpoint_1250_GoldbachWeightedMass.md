# Checkpoint 1250: Weighted upper main term: source outer products and total mass

# Weighted upper main term: source normalization and total error mass

The actual reciprocal mass over source pairs is bounded uniformly by a fixed constant times (log N)^7. The proof starts from the checked finite harmonic product estimate.

The original upper main-term sum is bounded by 24 B_R (1+K/log R) log R times the weighted Archimedean sum, plus its explicit total smoothing error. The lower main term is bounded below by 3 sqrt(9/8) (1-epsilon)^2 times the common reference C_R H_1(n) sqrt(log R/log N), whenever the two elementary relative error conditions hold.

Both results use the source's actual Euler products and singular integrals. The exact constant identity and arithmetic factors are preserved. The weighted upper comparison remains open pending the uniform relative errors and final assembly.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachWeightedMass.lean | 3 |
| GoldbachWeightedSourceOuter.lean | 2 |

- `goldbach_weighted_mass_constant_positive`
- `goldbach_weighted_mass_log_bound`
- `goldbach_weighted_arch_real_nonneg`
- `goldbach_weighted_upper_outer`
- `goldbach_weighted_lower_outer`

<!-- checkpoint-verification -->

## Verification

All 1354 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 5147-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 4419 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1356 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; all Section10 statements and the full circle-method implication are complete in the agreed conditional scope; Section11 remains open. Previously documented independent mean-value/Mertens inputs only. The full Section11 lower-sieve proposition p:sieveneedlower8 is a complete conditional implication, including its actual main term, uniform o(1), n-independent coefficients and mean-square error. The uniform main-term lower bound l:maintermsize8 and its joint application with the same large cutoff C are also complete conditionally. The weighted upper main-term sum, upper sieve, numerical comparison and final Goldbach conclusion remain open.

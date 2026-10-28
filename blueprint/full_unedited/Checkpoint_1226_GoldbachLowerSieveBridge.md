# Checkpoint 1226: Actual lower main term and circle remainder estimate

The actual lower sequence is now joined to the original arithmetic factor and smoothed singular integral. The base arithmetic factor is proved real and strictly positive at n=12 mod24; positivity of the singular integral proves X_n>=0 without a new assumption. CRT residue classes are fixed before n and are chosen to be units for every denominator. The exact real divisor-count identity and the sifted-count identity use the actual prime-square representations. The lower remainder sum is proved to satisfy the full N^4(log N)^(-A) mean-square bound, uniformly over every real coefficient family with absolute values at most1. This is a deduction from the existing ordinary SW/BV and Ren/Ghosh inputs, via the already checked circle-method theorem. The embedding d -> (1,24d), its injectivity, strict real modulus levels, reindexing and real-part norm comparison are all proved. A zero extension at denominator0 avoids an artificial zero-modulus term. The final presieve and limiting sieve-function assembly remain next. The selected manuscript is unchanged.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachLowerSieveBridge.lean | 6 |
| GoldbachLowerSieveRemainder.lean | 2 |

- `goldbach_lower_residue_properties`
- `goldbach_lower_residue_coprime`
- `goldbach_lower_base_real_positive`
- `goldbach_lower_main_term_nonneg`
- `goldbach_lower_divisor_real_identity`
- `goldbach_lower_sifted_sequence`
- `goldbach_lower_remainder_zero_extension`
- `goldbach_lower_remainder_mean_square`

<!-- checkpoint-verification -->

## Verification

All 1308 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 5101-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 4225 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1310 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; all Section10 statements and the full circle-method implication are complete in the agreed conditional scope; Section11 remains open. Existing independent classical inputs remain explicit. Classical interval Mertens products for the universal majorant and the progression3 mod4 are additional independent arithmetic inputs; no own-paper endpoint is assumed.

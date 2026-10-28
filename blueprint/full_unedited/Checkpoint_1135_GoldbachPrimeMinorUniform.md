# Checkpoint 1135: Uniform actual prime minor bound and the printed large-cutoff estimate

For each t > 0 and every C ≥ 6t+4d+8, one natural N₀ ≥ 4 now gives the actual uniform circle estimate |P_U(θ)| ≤ Z N(log N)^(-t) on the literal source minor arcs, simultaneously for all real 0 ≤ U ≤ N. Quotient representatives are handled explicitly, so this is a theorem about the circle polynomial, not a chosen real lift. The threshold is independent of U, W, θ and all progression/coefficient data. Taking t=3s+1 also proves the stronger displayed source estimate |P_U| ≤ Z (U/log U)(log N)^(-s) whenever 2 ≤ U ≤ N and U ≥ N(log N)^(-2s). Thus the printed large-cutoff prime estimate is covered as well as the bound needed for Bessel. Only the existing raw UniformRenGhoshInputs is assumed.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachPrimeMinorUniform.lean | 4 |

- `goldbachMinorRadiusThreshold_pos`
- `goldbach_prime_minor_uniform`
- `goldbach_prime_minor_source_cutoff_algebra`
- `goldbach_prime_minor_source_high_range`

<!-- checkpoint-verification -->

## Verification

All 1202 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4993-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 3719 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1204 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; the Section10/11 analytic and sieve estimates remain open internal obligations. The rational smooth multifrequency theorem with circle transference remains an explicit independent compound hypothesis. The classical primitive sum-of-two-squares criterion is an additional explicit independent arithmetic hypothesis for Section9 reductions; it contains no own-paper conclusion and is not declared as a Lean axiom.

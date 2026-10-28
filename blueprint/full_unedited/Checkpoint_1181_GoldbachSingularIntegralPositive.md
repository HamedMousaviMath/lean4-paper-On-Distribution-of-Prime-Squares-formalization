# Checkpoint 1181: Actual singular integral positivity for every arithmetic index

The genuine source H_(ell,R)(n;U,W) is now defined using the actual normalized seed cutoff, the exact quadratic integral and the strict progression-domain linear integral.

The product I_U J_(ell,W) is proved equal to its actual positive two-variable density Fourier integral. Substituting that identity into the proved Fubini theorem, and using the already-proved inverse positivity of eta_N squared, proves that H is real and nonnegative. This holds for every real n, all positive ell,N,R, and U,W≥2. If the strict progression domain is empty, the integral is exactly zero; this case is explicitly proved, so no upper bound on ell is hidden in the result.

Thus the full positivity clause of l:positiveH9 is proved. The O(N/sqrt(R)) comparison with the printed one-variable H_ell still needs its quantitative estimate and exact unsmoothed Fourier inversion. The lemma remains open in the ledger until both clauses are complete.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachSingularIntegralPositive.lean | 4 |

- `goldbach_euclidean_product_density`
- `goldbach_singular_integral_positive`
- `goldbach_singular_integral_empty`
- `goldbach_singular_integral_nonnegative`

<!-- checkpoint-verification -->

## Verification

All 1248 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 5041-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 3947 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1250 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; the Section10/11 analytic and sieve estimates remain open internal obligations. The rational smooth multifrequency theorem with circle transference remains an explicit independent compound hypothesis. The classical primitive sum-of-two-squares criterion is an additional explicit independent arithmetic hypothesis for Section9 reductions; it contains no own-paper conclusion and is not declared as a Lean axiom.

# Checkpoint 1116: Actual Goldbach minor-arc Bessel reduction and error assembly

The actual weighted progression sum is now defined with arbitrary complex coefficients and residues. The arithmetic-index set has precisely positive ell<L and positive k<V(ell), with strict arbitrary real cutoffs. Its membership equivalence is proved. The exact weighted Fourier identity and the full representation-count specialization are proved by finite linearity, not assumed.

The new goldbach_finite_fourier_bessel is a genuine finite Bessel inequality for arbitrary square-integrable circle functions, deduced from Mathlib's complete Fourier basis and the actual toLp representative. The set-restricted version applies to every measurable minor set and continuous prime/progression polynomials. It proves the literal bound sum_n |integral_minor P F e(-n theta)|^2 <= B^2 integral_circle |F|^2 from the pointwise bound |P|<=B on that set. Arbitrary finite integer output sets are allowed, so restriction to the paper's n<N^2 range costs nothing.

The theorem goldbach_actual_minor_bessel specializes this to the literal prime-square and weighted progression sums. A remaining bound on the actual progression energy is an INTERNAL proof obligation, as is the source's use of the independent raw prime exponential-sum estimate. Neither is renamed an external theorem. No logarithmic-saving hybrid estimate is claimed yet.

The exact major/minor decomposition of the weighted prime-pair count is proved for every measurable major set. The finite three-stage mean-square assembly proves the factor three in the source argument from the three successive INTERNAL error estimates. This assembles estimates once proved; it does not prove any of them by assumption. All eight supporting theorems use no new external deep input. The Bombieri–Vinogradov source lemma and the headline Goldbach theorem remain open.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachMinorArcBessel.lean | 8 |

- `mem_goldbachCoefficientIndices`
- `goldbach_weighted_fourier_inversion`
- `goldbach_weighted_full_fourier_inversion`
- `goldbach_finite_fourier_bessel`
- `goldbach_restricted_fourier_bessel`
- `goldbach_actual_minor_bessel`
- `goldbach_major_minor_partition`
- `goldbach_circle_three_stage_bound`

<!-- checkpoint-verification -->

## Verification

All 1183 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4974-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 3625 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1185 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; the Section10/11 analytic and sieve estimates remain open internal obligations. The rational smooth multifrequency theorem with circle transference remains an explicit independent compound hypothesis. The classical primitive sum-of-two-squares criterion is an additional explicit independent arithmetic hypothesis for Section9 reductions; it contains no own-paper conclusion and is not declared as a Lean axiom.

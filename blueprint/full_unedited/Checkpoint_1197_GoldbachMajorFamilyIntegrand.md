# Checkpoint 1197: Actual local arithmetic-family major integrand and compact support

The genuine local major-family integrand is now defined from the actual principal Gauss coefficient, Upsilon progression coefficient, bounded family coefficients and Euclidean I_U,J_(ell,W). Its exact source-family norm is proved at most A_q E_N(gamma), where A_q=9 exp(2) tau(q)^6 (log N)^2/(q sqrt(q)). This uses the individual primitive Upsilon decay and the full harmonic-family estimate, with arbitrary integer coprime residues.

The integrand is proved strongly measurable. Multiplication by the actual eta_N squared preserves the norm bound and strong measurability. The smoothed integrand is proved exactly zero for|gamma|≥R/(4N²), directly from the original seed support. Every arithmetic index and strict source family cutoff is retained.

The already-proved envelope energy and disjoint Bessel theorem can now be applied to these actual local functions. The source major-completion and final circle-method endpoints remain open until the denominator sums and exact Fourier identities are assembled.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachMajorFamilyIntegrand.lean | 6 |

- `goldbach_major_arithmetic_prefactor_nonnegative`
- `goldbach_major_family_integrand_measurable`
- `goldbach_major_family_integrand_bound`
- `goldbach_smooth_major_family_measurable`
- `goldbach_smooth_major_family_norm`
- `goldbach_smooth_major_family_support`

<!-- checkpoint-verification -->

## Verification

All 1264 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 5057-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 4017 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1266 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; the Section10/11 analytic and sieve estimates remain open internal obligations. The rational smooth multifrequency theorem with circle transference remains an explicit independent compound hypothesis. The classical primitive sum-of-two-squares criterion is an additional explicit independent arithmetic hypothesis for Section9 reductions; it contains no own-paper conclusion and is not declared as a Lean axiom.

# Checkpoint 1159: Restricted Bessel assembly for the two major-arc replacements

The restricted Bessel inequality is proved for arbitrary measurable circle functions in L², by applying the finite Fourier Bessel inequality to their indicators. A uniform major-arc error costs the normalized measure of the major arcs. A bounded measurable multiplier costs its squared bound times the full progression energy.

For the actual two-factor replacement, the exact identity PF−QG=Q(F−G)+(P−Q)F is integrated and the two squared errors are bounded by 2(BQ² BE² μ(major)+BP² E). All integrability and finite Fourier summations are proved. No endpoint approximation is assumed. The independent ordinary SW and BV inputs are not used by this general assembly theorem.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachMajorBesselAssembly.lean | 4 |

- `goldbach_restricted_function_bessel`
- `goldbach_restricted_uniform_bessel`
- `goldbach_restricted_measurable_multiplier_bessel`
- `goldbach_two_model_major_bessel`

<!-- checkpoint-verification -->

## Verification

All 1226 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 5017-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 3840 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1228 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; the Section10/11 analytic and sieve estimates remain open internal obligations. The rational smooth multifrequency theorem with circle transference remains an explicit independent compound hypothesis. The classical primitive sum-of-two-squares criterion is an additional explicit independent arithmetic hypothesis for Section9 reductions; it contains no own-paper conclusion and is not declared as a Lean axiom.

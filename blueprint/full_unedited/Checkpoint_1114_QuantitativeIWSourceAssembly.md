# Checkpoint 1114: Complete all four quantitative IW clauses and close Sections 3–8 deductions

# Full quantitative IW proposition: completed conditional deduction at checkpoint1114

The final theorem is proposition_quantitative_IW_full in PrimeSquares/QuantitativeIWSourceAssembly.lean. It chooses one arithmetic construction before the multiplier, p, complex measure, sampled input and target space. It is a complete implication under explicitly named independent general inputs, not an unconditional proof of Tao's theorems.

| Source clause | Matched checked scope |
| --- | --- |
| (i), construction | Every real Q>=2^k, r>=2 and k>=4; exactly B=C^(k^2 Q^(1/(k-1/2))) and epsilon=(2^20 r B^(2r+8))^(-1); one positive integer P<=3^Q; every a/q modulo one for all integers a and all positive q<=Q, including unreduced fractions; all reduced denominators <=B; full (r,1/2)-goodness. |
| (ii), multiplier | Arbitrary essentially bounded measurable real symbols supported almost everywhere in the closed narrow interval, arbitrary complex cyclic measures of total variation <=1, and every p in [p_r,2r]. The real norm is that of an operator on the whole real Lp space. The conclusion is an actual bounded operator on the whole integer lp space, with the literal projected inverse-Fourier convolution kernel and norm <=C_rk times the full real operator norm. Agreement on finite inputs determines this entire operator uniquely. No smoothness or L2-intersection restriction is substituted for the full operator. |
| (iii), major-arc sampling | The complete distributional Fourier-support lp class, both norm directions, the literal inverse-C_rk lower bound, unique interpolation and its exact sampled diagonal. The positive-exponent typeclass is proved from p>=p_r>1, not a new mathematical hypothesis. The normalized finite cyclic norm agrees with the earlier iterated real/cyclic norm. |
| (iv), Shannon sampling | Every finite-dimensional normed complex target, every extended exponent 1<=p<=infinity, every positive delta<=1/(100P), full real Lp fibres with distributional Fourier support, actual diagonal lp membership and both norm directions with one absolute sampling constant. No Hilbert, p<=2 or Schwartz restriction remains. |

For point sampling, bandlimited functions are evaluated in their continuous representatives, as in the standard sampling convention. This does not impose Schwartz decay, integrability or L2 membership. An arbitrary modification of an Lp representative at individual points cannot define the sampling operator.

The real Fourier support is expressed using Mathlib's actual tempered-distribution Fourier transform. The integer support is expressed by its literal Schwartz-test Fourier series; absolute convergence is proved for every lp input. The finite cyclic Fourier basis is exactly the P-torsion rational set, not all denominators <=P. Its correction at1112 has exact source hashes and a complete dependency rebuild/audit; the final theorem explicitly proves every IW frequency belongs to the corrected basis.

The independent unproved inputs are RawTaoArcConstructionInput, RawFullAdelicIWInput, RawFullMajorArcSamplingInput and RawFullShannonInput. The last three general statements explicitly include their published-to-full-class/finite-quotient/kernel bridges; the general rough-symbol limiting argument is also not formalized. They quantify over arbitrary good coprime data or arbitrary narrow cyclic data, not the paper's chosen Q, probability measure, annular model, low/high estimate or maximal conclusion. The full real Lp product bound, coefficient specialization, exact construction applicability and source assembly are proved deductions. Checking their consuming implications does not prove these independent hypotheses true.

The earlier endpoint theorems retain their previously recorded, narrower assumptions. This broad standalone completion does not retroactively add the full-domain hypotheses to them. The Goldbach circle-method and sieve estimates remain open internal paper obligations.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| QuantitativeIWSourceAssembly.lean | 9 |

- `iw_frequency_in_cyclic_basis`
- `rational_fract_circle`
- `iw_coverage_all_rational_lifts`
- `iw_coverage_all_fraction_points`
- `fullIntegerKernelMultiplier_single`
- `fullIntegerKernelMultiplier_unique`
- `iw_source_exponent_one_le`
- `full_iw_source_analytic_clauses`
- `proposition_quantitative_IW_full`

<!-- checkpoint-verification -->

## Verification

All 1181 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4972-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 3609 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1183 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; the Section10/11 analytic and sieve estimates remain open internal obligations. The rational smooth multifrequency theorem with circle transference remains an explicit independent compound hypothesis. The classical primitive sum-of-two-squares criterion is an additional explicit independent arithmetic hypothesis for Section9 reductions; it contains no own-paper conclusion and is not declared as a Lean axiom.

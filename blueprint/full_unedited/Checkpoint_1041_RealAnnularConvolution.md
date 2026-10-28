# Checkpoint 1041: All-input real annular convolution and continuity in scale

For arbitrary Lp inputs with p>=1, Lean proves the real-scale annular convolution is measurable and dominated pointwise by the one-sided interval average. It checks the literal kernel-to-interval integral identity and proves continuity in the real scale parameter at every spatial point, using a locally integrable clamped power weight and continuous interval primitives. These facts enable a fixed countable dense set of real scales to represent the proper uncountable maximum, rather than interchanging uncountably many almost-everywhere assertions. No external input is used in this checkpoint.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| RealAnnularConvolution.lean | 7 |

- `shiftedLp_integrableOn`
- `realContinuousAnnularKernel_product_box`
- `realContinuousAnnularConvolution_box_bound`
- `realContinuousAnnularConvolution_aestronglyMeasurable`
- `realAnnularPrimitiveIntegrand_locallyIntegrable`
- `realContinuousAnnularConvolution_interval`
- `realContinuousAnnularConvolution_continuous_scale`

<!-- checkpoint-verification -->

## Verification

All 1108 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4899-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 3269 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1110 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The user confirmed the three Section8 edits; the selected project manuscript contains their exact agreed reconstruction, with all numbered statements and labels unchanged and original sources preserved. Sections3/4 and Section8 retain their complete reviewed conditional scopes. The full approximation lemma and low proposition of Section6 are now exported with exact real-Q, all-input, all-real-radius and exponent quantifiers. Remaining Sections5–7 auxiliary claims are being reviewed and completed before Goldbach work. Deep general inputs remain explicit and unproved. Theorem7.2 consumes the precise independent scalar quadratic Weyl approximation (including its unproved selection/reduction/phase bridge), general Tao construction, IW multiplier, major-arc/Shannon sampling, continuous/interpolation, signed-sequence and smooth multifrequency inputs, Page uniqueness and compatible raw prime-distribution data. All own ordinary and prime circle approximations, quantitative low/high comparisons, restricted estimates, parameter optimization and final source assembly are proved. Corollary7.6 adds no independent input. Theorem1.5(ii) additionally consumes only general strong Calderon transference, with actual prime enumeration proved. Corollary7.46 additionally uses general strong/modular Calderon transference and bounded-class polynomial convergence, including its still-unformalized published-theorem/cutoff/PNT/Abel/prime-power normalization bridges. Own unbounded Orlicz/L1 density convergence and identification of both limits are proved. These Prop-valued independent inputs are unproved theorem parameters, not new Lean mathematical axioms. Earlier Theorems1.1/1.3 and Propositions4.19/6.21 retain their separate recorded inputs; older ordinary global/local stopping hypotheses are not consumed by this new ordinary IW route. Theorem1.5(i) uses only the precise general split-polynomial Weil, fixed-progression prime-frequency PNT, original LaVictoire weak-maximal-failure, Sawyer and Conze inputs. Their existence and exact published-to-Lean convention bridges remain unproved. The optional quoted general GK input has a precise interface and checked joint Poisson application, but is not consumed by badness. All current-paper arithmetic, moment, limit, frequency and persistence deductions are proved.

# Checkpoint 1040: Literal annular kernels at every real scale

Lean extends the actual continuous annular density and kernel to every positive real scale, with exact agreement at natural scales. It proves integrability, nonnegativity and the uniform box-kernel bound for every real N>=2, uniformly in beta<=1. This removes the first integer-scale restriction in the standalone continuous auxiliary lemma. The full uncountable maximum and its measurability, common almost-everywhere bound and Lp estimate are separate next deductions; this checkpoint does not prematurely award the full source lemma. No independent input is used for these real-scale kernel proofs.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| RealAnnularKernelBounds.lean | 7 |

- `realContinuousAnnularKernel_nat`
- `realAnnularKernelDensity_continuousOn`
- `realContinuousAnnularKernel_integrable`
- `realContinuousAnnularKernel_complex_integrable`
- `realContinuousAnnularKernel_nonneg`
- `realAnnularKernelDensity_bound`
- `realContinuousAnnularKernel_box_bound`

<!-- checkpoint-verification -->

## Verification

All 1107 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4898-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 3262 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1109 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The user confirmed the three Section8 edits; the selected project manuscript contains their exact agreed reconstruction, with all numbered statements and labels unchanged and original sources preserved. Sections3/4 and Section8 retain their complete reviewed conditional scopes. The full approximation lemma and low proposition of Section6 are now exported with exact real-Q, all-input, all-real-radius and exponent quantifiers. Remaining Sections5–7 auxiliary claims are being reviewed and completed before Goldbach work. Deep general inputs remain explicit and unproved. Theorem7.2 consumes the precise independent scalar quadratic Weyl approximation (including its unproved selection/reduction/phase bridge), general Tao construction, IW multiplier, major-arc/Shannon sampling, continuous/interpolation, signed-sequence and smooth multifrequency inputs, Page uniqueness and compatible raw prime-distribution data. All own ordinary and prime circle approximations, quantitative low/high comparisons, restricted estimates, parameter optimization and final source assembly are proved. Corollary7.6 adds no independent input. Theorem1.5(ii) additionally consumes only general strong Calderon transference, with actual prime enumeration proved. Corollary7.46 additionally uses general strong/modular Calderon transference and bounded-class polynomial convergence, including its still-unformalized published-theorem/cutoff/PNT/Abel/prime-power normalization bridges. Own unbounded Orlicz/L1 density convergence and identification of both limits are proved. These Prop-valued independent inputs are unproved theorem parameters, not new Lean mathematical axioms. Earlier Theorems1.1/1.3 and Propositions4.19/6.21 retain their separate recorded inputs; older ordinary global/local stopping hypotheses are not consumed by this new ordinary IW route. Theorem1.5(i) uses only the precise general split-polynomial Weil, fixed-progression prime-frequency PNT, original LaVictoire weak-maximal-failure, Sawyer and Conze inputs. Their existence and exact published-to-Lean convention bridges remain unproved. The optional quoted general GK input has a precise interface and checked joint Poisson application, but is not consumed by badness. All current-paper arithmetic, moment, limit, frequency and persistence deductions are proved.

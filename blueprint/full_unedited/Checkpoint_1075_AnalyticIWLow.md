# Checkpoint 1075: Low maximal proof under its precise analytic data requirements

The full IW low maximal proof is now checked for an analytic data structure requiring only positive pairwise coprime components, a common period, its size bound, and the component bound. Rational coverage is not a hypothesis of this analytic theorem. Twenty-two existing deductions have been generalized and freshly compiled, from goodness and multiplier/sampling estimates through the narrow, transition, remainder, finite-input, and all-input maximal estimates. This introduces no external input. The original arithmetic construction and its coverage theorem remain available separately; this separation will allow the exact real-Q cutoff to be retained rather than rounded. The full paper proposition is not claimed complete at this intermediate step.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| AnalyticIWLow.lean | 22 |

- `analytic_quantitative_iw_goodness`
- `analytic_quantitative_iw_multiplier`
- `analytic_quantitative_iw_sampling`
- `analytic_iw_finite_lift_size`
- `analytic_iwFiniteCutoffLift_size`
- `analytic_iw_narrow_finite_maximum`
- `analytic_iw_narrow_integer_majorant`
- `analytic_iw_annular_remainder_multiplier`
- `analytic_iw_large_remainder_majorant`
- `analytic_iw_annular_single_multiplier`
- `analytic_iw_signed_annular_multiplier`
- `analytic_iw_annular_signed_increments`
- `analytic_iw_short_scale_increment_maximum`
- `analytic_iw_short_scale_maximum`
- `analytic_iw_period_log_bound`
- `analytic_iw_narrow_log_inverse_budget`
- `analytic_iw_transition_index_linear_budget`
- `analytic_iw_transition_log_cost_budget`
- `analytic_iw_short_transition_cost_bound`
- `analytic_iw_short_transition_maximum`
- `analytic_iw_finite_input_low_majorant`
- `analytic_iw_full_low_maximal_bound`

<!-- checkpoint-verification -->

## Verification

All 1142 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4933-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 3422 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1144 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The accepted Section8, admissibility, dyadic sparse-scale and retained-dilation edits are reconstructed in the selected manuscript, with original source copies and every label preserved. Only the accepted definition and dyadic auxiliary statement change inside numbered environments; no new full user upload is claimed. The seven remaining auxiliaries are being proved from their normal source hypotheses and the explicitly recorded independent standard inputs. No own-paper conclusion is a new deep assumption. Section9 has not been started. Theorem7.2 consumes the precise independent scalar quadratic Weyl approximation (including its unproved selection/reduction/phase bridge), general Tao construction, IW multiplier, major-arc/Shannon sampling, continuous/interpolation, signed-sequence and smooth multifrequency inputs, Page uniqueness and compatible raw prime-distribution data. All own ordinary and prime circle approximations, quantitative low/high comparisons, restricted estimates, parameter optimization and final source assembly are proved. Corollary7.6 adds no independent input. Theorem1.5(ii) additionally consumes only general strong Calderon transference, with actual prime enumeration proved. Corollary7.46 additionally uses general strong/modular Calderon transference and bounded-class polynomial convergence, including its still-unformalized published-theorem/cutoff/PNT/Abel/prime-power normalization bridges. Own unbounded Orlicz/L1 density convergence and identification of both limits are proved. These Prop-valued independent inputs are unproved theorem parameters, not new Lean mathematical axioms. Earlier Theorems1.1/1.3 and Propositions4.19/6.21 retain their separate recorded inputs; older ordinary global/local stopping hypotheses are not consumed by this new ordinary IW route. Theorem1.5(i) uses only the precise general split-polynomial Weil, fixed-progression prime-frequency PNT, original LaVictoire weak-maximal-failure, Sawyer and Conze inputs. Their existence and exact published-to-Lean convention bridges remain unproved. The optional quoted general GK input has a precise interface and checked joint Poisson application, but is not consumed by badness. All current-paper arithmetic, moment, limit, frequency and persistence deductions are proved.

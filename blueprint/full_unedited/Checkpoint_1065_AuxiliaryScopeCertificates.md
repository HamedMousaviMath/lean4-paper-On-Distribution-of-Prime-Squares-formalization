# Checkpoint 1065: Consolidated pre-Goldbach source review with exact scope certificates

The pre-Goldbach source review is consolidated with exact Lean scope certificates. A nonnegative density profile disproves the blanket fixed-dilation comparison for arbitrary Psi in the sparse-recursion proof; the corrected dyadic recursion can retain the displayed dilated form, but still needs its proof. Two scalar certificates show why a logarithm-squared estimate cannot be relabeled as a first-power estimate by changing a constant. They do not assert a counterexample to the special sharper annular theorem. The source review records five newly completed numbered auxiliaries, seven precise remaining claims, the exact real-Q IW extension, and the separately proposed one-sided admissibility clarification. Section9 has not been started. No new independent analytic input is introduced.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| AuxiliaryScopeCertificates.lean | 4 |

- `quadratic_log_loss_not_linear`
- `cubic_log_loss_not_quadratic`
- `densityProfileSpike_nonneg`
- `densityProfileSpike_no_dilation_comparison`

<!-- checkpoint-verification -->

## Verification

All 1132 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4923-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 3361 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1134 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The user confirmed the three Section8 edits; the selected project manuscript contains their exact agreed reconstruction, with all numbered statements and labels unchanged and original sources preserved. Sections3/4 and Section8 retain their complete reviewed conditional scopes. The full approximation lemma and low proposition of Section6 are now exported with exact real-Q, all-input, all-real-radius and exponent quantifiers. Remaining Sections5–7 auxiliary claims are being reviewed and completed before Goldbach work. Deep general inputs remain explicit and unproved. Theorem7.2 consumes the precise independent scalar quadratic Weyl approximation (including its unproved selection/reduction/phase bridge), general Tao construction, IW multiplier, major-arc/Shannon sampling, continuous/interpolation, signed-sequence and smooth multifrequency inputs, Page uniqueness and compatible raw prime-distribution data. All own ordinary and prime circle approximations, quantitative low/high comparisons, restricted estimates, parameter optimization and final source assembly are proved. Corollary7.6 adds no independent input. Theorem1.5(ii) additionally consumes only general strong Calderon transference, with actual prime enumeration proved. Corollary7.46 additionally uses general strong/modular Calderon transference and bounded-class polynomial convergence, including its still-unformalized published-theorem/cutoff/PNT/Abel/prime-power normalization bridges. Own unbounded Orlicz/L1 density convergence and identification of both limits are proved. These Prop-valued independent inputs are unproved theorem parameters, not new Lean mathematical axioms. Earlier Theorems1.1/1.3 and Propositions4.19/6.21 retain their separate recorded inputs; older ordinary global/local stopping hypotheses are not consumed by this new ordinary IW route. Theorem1.5(i) uses only the precise general split-polynomial Weil, fixed-progression prime-frequency PNT, original LaVictoire weak-maximal-failure, Sawyer and Conze inputs. Their existence and exact published-to-Lean convention bridges remain unproved. The optional quoted general GK input has a precise interface and checked joint Poisson application, but is not consumed by badness. All current-paper arithmetic, moment, limit, frequency and persistence deductions are proved.

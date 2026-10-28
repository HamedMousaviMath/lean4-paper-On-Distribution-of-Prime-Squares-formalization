# Checkpoint 1045: Literal linear-scale admissibility and exact finite window counts

The literal linear-scale local average and its supremum over every real radius are now formalized on actual l1 inputs, with convergence, positivity at positive scales and uniform bounds. For indicator inputs Lean proves the exact finite window-count formula and exports the source admissible dyadic stopping-map condition as an equivalence with its displayed all-real-radius finite-count inequality. This supplies the missing concrete admissibility objects for the general Section5 argument. No analytic or own-paper conclusion is an assumed input. Completion of the definition's additional convention remarks is not claimed here.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| LinearLocalMass.lean | 10 |

- `linearSourceBall_summable`
- `linearSourceBallMass_nonneg`
- `linearSourceBallMass_uniform`
- `linearSourceLocalMass_bddAbove`
- `linearSourceBallMass_le_local`
- `linearSourceLocalMass_nonneg`
- `linearSourceLocalMass_uniform`
- `linearSourceLocalMass_le_iff`
- `linearSourceBallMass_indicator`
- `sourceLinearAdmissible_iff_display`

<!-- checkpoint-verification -->

## Verification

All 1112 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4903-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 3292 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1114 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The user confirmed the three Section8 edits; the selected project manuscript contains their exact agreed reconstruction, with all numbered statements and labels unchanged and original sources preserved. Sections3/4 and Section8 retain their complete reviewed conditional scopes. The full approximation lemma and low proposition of Section6 are now exported with exact real-Q, all-input, all-real-radius and exponent quantifiers. Remaining Sections5–7 auxiliary claims are being reviewed and completed before Goldbach work. Deep general inputs remain explicit and unproved. Theorem7.2 consumes the precise independent scalar quadratic Weyl approximation (including its unproved selection/reduction/phase bridge), general Tao construction, IW multiplier, major-arc/Shannon sampling, continuous/interpolation, signed-sequence and smooth multifrequency inputs, Page uniqueness and compatible raw prime-distribution data. All own ordinary and prime circle approximations, quantitative low/high comparisons, restricted estimates, parameter optimization and final source assembly are proved. Corollary7.6 adds no independent input. Theorem1.5(ii) additionally consumes only general strong Calderon transference, with actual prime enumeration proved. Corollary7.46 additionally uses general strong/modular Calderon transference and bounded-class polynomial convergence, including its still-unformalized published-theorem/cutoff/PNT/Abel/prime-power normalization bridges. Own unbounded Orlicz/L1 density convergence and identification of both limits are proved. These Prop-valued independent inputs are unproved theorem parameters, not new Lean mathematical axioms. Earlier Theorems1.1/1.3 and Propositions4.19/6.21 retain their separate recorded inputs; older ordinary global/local stopping hypotheses are not consumed by this new ordinary IW route. Theorem1.5(i) uses only the precise general split-polynomial Weil, fixed-progression prime-frequency PNT, original LaVictoire weak-maximal-failure, Sawyer and Conze inputs. Their existence and exact published-to-Lean convention bridges remain unproved. The optional quoted general GK input has a precise interface and checked joint Poisson application, but is not consumed by badness. All current-paper arithmetic, moment, limit, frequency and persistence deductions are proved.

# Checkpoint 1053: The physical-scale and radius export of the abstract local lemma

The source conventions for the abstract stopping estimate are now exported: physical dyadic values are recovered exactly from their exponents, arbitrary positive admissibility radii are compared, support size in a fixed dilation is replaced by its explicit uniform density cap, and the parent interval length is the normalization. Lean proves the exact equivalence of the source splitting range J<=M^((1-v)/s)/10 with the threshold used by the proof and identifies M^(1-v) times the local average with the literal M^(-v) window count. The terminal source endpoint has the printed exponents and a constant chosen before all interval, set, stopping and operator data. A final Fourier-symbol-to-operator bridge is being added before awarding the printed source lemma completion.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| SourceAbstractLocalStopping.lean | 4 |

- `localSplittingThreshold_le_iff`
- `linearSourceBallMass_indicator_power`
- `source_local_stopping_density_cap`
- `source_abstract_local_stopping_estimate`

<!-- checkpoint-verification -->

## Verification

All 1120 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4911-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 3315 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1122 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The user confirmed the three Section8 edits; the selected project manuscript contains their exact agreed reconstruction, with all numbered statements and labels unchanged and original sources preserved. Sections3/4 and Section8 retain their complete reviewed conditional scopes. The full approximation lemma and low proposition of Section6 are now exported with exact real-Q, all-input, all-real-radius and exponent quantifiers. Remaining Sections5–7 auxiliary claims are being reviewed and completed before Goldbach work. Deep general inputs remain explicit and unproved. Theorem7.2 consumes the precise independent scalar quadratic Weyl approximation (including its unproved selection/reduction/phase bridge), general Tao construction, IW multiplier, major-arc/Shannon sampling, continuous/interpolation, signed-sequence and smooth multifrequency inputs, Page uniqueness and compatible raw prime-distribution data. All own ordinary and prime circle approximations, quantitative low/high comparisons, restricted estimates, parameter optimization and final source assembly are proved. Corollary7.6 adds no independent input. Theorem1.5(ii) additionally consumes only general strong Calderon transference, with actual prime enumeration proved. Corollary7.46 additionally uses general strong/modular Calderon transference and bounded-class polynomial convergence, including its still-unformalized published-theorem/cutoff/PNT/Abel/prime-power normalization bridges. Own unbounded Orlicz/L1 density convergence and identification of both limits are proved. These Prop-valued independent inputs are unproved theorem parameters, not new Lean mathematical axioms. Earlier Theorems1.1/1.3 and Propositions4.19/6.21 retain their separate recorded inputs; older ordinary global/local stopping hypotheses are not consumed by this new ordinary IW route. Theorem1.5(i) uses only the precise general split-polynomial Weil, fixed-progression prime-frequency PNT, original LaVictoire weak-maximal-failure, Sawyer and Conze inputs. Their existence and exact published-to-Lean convention bridges remain unproved. The optional quoted general GK input has a precise interface and checked joint Poisson application, but is not consumed by badness. All current-paper arithmetic, moment, limit, frequency and persistence deductions are proved.

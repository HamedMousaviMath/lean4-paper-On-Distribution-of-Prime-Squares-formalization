# Checkpoint 1070: General finite sparse recursion for an arbitrary density profile

The general finite sparse recursion is proved from the local stopping-time hypothesis for arbitrary positive compact-support dyadic convolution families. The output has actual intervals and disjoint major subsets of at least three quarters their lengths. The exact density-profile cost uses F intersected with the fixed dilation and G intersected with the parent, divided by the parent length. Psi is arbitrary: no positivity, monotonicity or dilation-comparison property is added. Every recursive call shortens the interval, so termination and the cost sum are checked. Removing the outer scale truncation remains a separate proof step.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GenericFiniteSparse.lean | 3 |

- `genericPositiveSparseStep`
- `genericPositiveFiniteSparse`
- `genericFiniteSparse_from_local_profile`

<!-- checkpoint-verification -->

## Verification

All 1137 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4928-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 3385 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1139 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The accepted Section8, admissibility, dyadic sparse-scale and retained-dilation edits are reconstructed in the selected manuscript, with original source copies and every label preserved. Only the accepted definition and dyadic auxiliary statement change inside numbered environments; no new full user upload is claimed. The seven remaining auxiliaries are being proved from their normal source hypotheses and the explicitly recorded independent standard inputs. No own-paper conclusion is a new deep assumption. Section9 has not been started. Theorem7.2 consumes the precise independent scalar quadratic Weyl approximation (including its unproved selection/reduction/phase bridge), general Tao construction, IW multiplier, major-arc/Shannon sampling, continuous/interpolation, signed-sequence and smooth multifrequency inputs, Page uniqueness and compatible raw prime-distribution data. All own ordinary and prime circle approximations, quantitative low/high comparisons, restricted estimates, parameter optimization and final source assembly are proved. Corollary7.6 adds no independent input. Theorem1.5(ii) additionally consumes only general strong Calderon transference, with actual prime enumeration proved. Corollary7.46 additionally uses general strong/modular Calderon transference and bounded-class polynomial convergence, including its still-unformalized published-theorem/cutoff/PNT/Abel/prime-power normalization bridges. Own unbounded Orlicz/L1 density convergence and identification of both limits are proved. These Prop-valued independent inputs are unproved theorem parameters, not new Lean mathematical axioms. Earlier Theorems1.1/1.3 and Propositions4.19/6.21 retain their separate recorded inputs; older ordinary global/local stopping hypotheses are not consumed by this new ordinary IW route. Theorem1.5(i) uses only the precise general split-polynomial Weil, fixed-progression prime-frequency PNT, original LaVictoire weak-maximal-failure, Sawyer and Conze inputs. Their existence and exact published-to-Lean convention bridges remain unproved. The optional quoted general GK input has a precise interface and checked joint Poisson application, but is not consumed by badness. All current-paper arithmetic, moment, limit, frequency and persistence deductions are proved.

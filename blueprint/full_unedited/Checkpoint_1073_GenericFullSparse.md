# Checkpoint 1073: The full general dyadic sparse implication with an arbitrary density profile

The general untruncated dyadic sparse implication is proved for every positive compact-support convolution family and arbitrary density profile. Lean constructs a finite root containing the input, testing points and the finitely selected scales, applies the terminating recursion, and obtains actual quarter-sparse major subsets. The constant is exactly twice the local testing constant and is uniform over all finite input and testing sets. No monotone Psi, scale decay, attained infinite maximum, limiting sparse family, or current-paper sparse conclusion is assumed. The final wrapper still checks the source convention that stopping maps are admissible on the entire parent interval.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GenericFullSparse.lean | 5 |

- `genericFiniteTestRoot_contains`
- `genericFiniteTestRoot_scales`
- `genericFiniteTest_le_root`
- `genericPositiveFullSparse`
- `source_dyadic_sparse_recursion`

<!-- checkpoint-verification -->

## Verification

All 1140 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4931-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 3398 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1142 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The accepted Section8, admissibility, dyadic sparse-scale and retained-dilation edits are reconstructed in the selected manuscript, with original source copies and every label preserved. Only the accepted definition and dyadic auxiliary statement change inside numbered environments; no new full user upload is claimed. The seven remaining auxiliaries are being proved from their normal source hypotheses and the explicitly recorded independent standard inputs. No own-paper conclusion is a new deep assumption. Section9 has not been started. Theorem7.2 consumes the precise independent scalar quadratic Weyl approximation (including its unproved selection/reduction/phase bridge), general Tao construction, IW multiplier, major-arc/Shannon sampling, continuous/interpolation, signed-sequence and smooth multifrequency inputs, Page uniqueness and compatible raw prime-distribution data. All own ordinary and prime circle approximations, quantitative low/high comparisons, restricted estimates, parameter optimization and final source assembly are proved. Corollary7.6 adds no independent input. Theorem1.5(ii) additionally consumes only general strong Calderon transference, with actual prime enumeration proved. Corollary7.46 additionally uses general strong/modular Calderon transference and bounded-class polynomial convergence, including its still-unformalized published-theorem/cutoff/PNT/Abel/prime-power normalization bridges. Own unbounded Orlicz/L1 density convergence and identification of both limits are proved. These Prop-valued independent inputs are unproved theorem parameters, not new Lean mathematical axioms. Earlier Theorems1.1/1.3 and Propositions4.19/6.21 retain their separate recorded inputs; older ordinary global/local stopping hypotheses are not consumed by this new ordinary IW route. Theorem1.5(i) uses only the precise general split-polynomial Weil, fixed-progression prime-frequency PNT, original LaVictoire weak-maximal-failure, Sawyer and Conze inputs. Their existence and exact published-to-Lean convention bridges remain unproved. The optional quoted general GK input has a precise interface and checked joint Poisson application, but is not consumed by badness. All current-paper arithmetic, moment, limit, frequency and persistence deductions are proved.

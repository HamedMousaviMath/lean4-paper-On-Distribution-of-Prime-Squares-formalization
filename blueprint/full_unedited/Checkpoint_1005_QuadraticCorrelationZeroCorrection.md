# Checkpoint 1005: Exact finite correlation and zero-location correction

Lean proves that the literal finite quadratic-residue correlation equals the sum of exact indicator products. It proves the complete zero correction between that hard count and the soft character-product count: the soft count is larger, and its excess is at most the number of distinct shifts. Every zero location is counted explicitly by a finite double sum. No Weil input is needed for this correction.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| QuadraticCorrelationZeroCorrection.lean | 5 |

- `quadraticCorrelation_as_product`
- `quadraticSoft_product_nonneg`
- `quadraticSoft_product_le_one`
- `quadraticSoft_product_correction`
- `quadraticSoftCorrelation_error`

<!-- checkpoint-verification -->

## Verification

All 1072 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4862-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 3090 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1074 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

Theorem7.2, Corollaries7.6/7.46 and Theorem1.5(ii) are complete checked implications under their explicitly recorded independent inputs. This includes the actual full maximal operators, quantitative strong and modular bounds, own Orlicz pointwise/L1 convergence and exact prime enumeration. Theorem1.5(i) remains open, so its whole source entry is partial. Earlier Theorems1.1/1.3, Propositions4.19/6.21 and reflection retain their reviewed scopes. Stronger standalone auxiliary statements and later arithmetic applications remain separately unfinished. Theorem7.2 consumes the precise independent scalar quadratic Weyl approximation (including its unproved selection/reduction/phase bridge), general Tao construction, IW multiplier, major-arc/Shannon sampling, continuous/interpolation, signed-sequence and smooth multifrequency inputs, Page uniqueness and compatible raw prime-distribution data. All own ordinary and prime circle approximations, quantitative low/high comparisons, restricted estimates, parameter optimization and final source assembly are proved. Corollary7.6 adds no independent input. Theorem1.5(ii) additionally consumes only general strong Calderon transference, with actual prime enumeration proved. Corollary7.46 additionally uses general strong/modular Calderon transference and bounded-class polynomial convergence, including its still-unformalized published-theorem/cutoff/PNT/Abel/prime-power normalization bridges. Own unbounded Orlicz/L1 density convergence and identification of both limits are proved. These Prop-valued independent inputs are unproved theorem parameters, not new Lean mathematical axioms. Earlier Theorems1.1/1.3 and Propositions4.19/6.21 retain their separate recorded inputs; older ordinary global/local stopping hypotheses are not consumed by this new ordinary IW route.

# Checkpoint 1022: Actual prime-product difference bound and same-modulus finite repair

Lean proves the actual prime-product far-pair lower bound 1-6*gamma-3*rho_q from the checked triple moment and exact signed-shift cover. It assembles this with the actual thickening bounds for the same residue set, modulus and finite error budget, and checks the source alpha=1/160 margin for gamma<1/16. The remaining arithmetic construction must supply the finite budget and radius assumptions; no Poisson spacing or false strict fraction inequality is used.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| PrimeProductDifference.lean | 3 |

- `prime_product_far_pair_bound`
- `prime_product_finite_badness_conditions`
- `badness_difference_constant_margin`

<!-- checkpoint-verification -->

## Verification

All 1089 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4879-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 3173 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1091 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

Theorem7.2, Corollaries7.6/7.46 and Theorem1.5(ii) are complete checked implications under their explicitly recorded independent inputs. This includes the actual full maximal operators, quantitative strong and modular bounds, own Orlicz pointwise/L1 convergence and exact prime enumeration. Theorem1.5(i) remains open, so its whole source entry is partial. Earlier Theorems1.1/1.3, Propositions4.19/6.21 and reflection retain their reviewed scopes. Stronger standalone auxiliary statements and later arithmetic applications remain separately unfinished. Theorem7.2 consumes the precise independent scalar quadratic Weyl approximation (including its unproved selection/reduction/phase bridge), general Tao construction, IW multiplier, major-arc/Shannon sampling, continuous/interpolation, signed-sequence and smooth multifrequency inputs, Page uniqueness and compatible raw prime-distribution data. All own ordinary and prime circle approximations, quantitative low/high comparisons, restricted estimates, parameter optimization and final source assembly are proved. Corollary7.6 adds no independent input. Theorem1.5(ii) additionally consumes only general strong Calderon transference, with actual prime enumeration proved. Corollary7.46 additionally uses general strong/modular Calderon transference and bounded-class polynomial convergence, including its still-unformalized published-theorem/cutoff/PNT/Abel/prime-power normalization bridges. Own unbounded Orlicz/L1 density convergence and identification of both limits are proved. These Prop-valued independent inputs are unproved theorem parameters, not new Lean mathematical axioms. Earlier Theorems1.1/1.3 and Propositions4.19/6.21 retain their separate recorded inputs; older ordinary global/local stopping hypotheses are not consumed by this new ordinary IW route.

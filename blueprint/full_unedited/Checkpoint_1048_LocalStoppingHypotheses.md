# Checkpoint 1048: Exact hypotheses and small scales for the abstract stopping lemma

The full abstract local hypotheses are encoded as bounds on the actual operator family, its low/high/error pieces, and the real-radius linear local average. The record contains neither a stopping pairing estimate nor an endpoint conclusion. The physical scale is 2^j, the splitting threshold is exactly (10J)^(s/(1-v)), and Lean proves the small-scale estimate with the printed powers of J and log J. This exposes the full mathematical assumptions needed for the general Section5 local argument rather than replacing it by the already-proved prime-square instance. No analytic input or new axiom is introduced.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| LocalStoppingHypotheses.lean | 4 |

- `localSplittingThreshold_power`
- `small_local_scale_growth`
- `local_small_scale_log_absorption`
- `localStopping_small_pointwise`

<!-- checkpoint-verification -->

## Verification

All 1115 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4906-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 3301 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1117 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The user confirmed the three Section8 edits; the selected project manuscript contains their exact agreed reconstruction, with all numbered statements and labels unchanged and original sources preserved. Sections3/4 and Section8 retain their complete reviewed conditional scopes. The full approximation lemma and low proposition of Section6 are now exported with exact real-Q, all-input, all-real-radius and exponent quantifiers. Remaining Sections5–7 auxiliary claims are being reviewed and completed before Goldbach work. Deep general inputs remain explicit and unproved. Theorem7.2 consumes the precise independent scalar quadratic Weyl approximation (including its unproved selection/reduction/phase bridge), general Tao construction, IW multiplier, major-arc/Shannon sampling, continuous/interpolation, signed-sequence and smooth multifrequency inputs, Page uniqueness and compatible raw prime-distribution data. All own ordinary and prime circle approximations, quantitative low/high comparisons, restricted estimates, parameter optimization and final source assembly are proved. Corollary7.6 adds no independent input. Theorem1.5(ii) additionally consumes only general strong Calderon transference, with actual prime enumeration proved. Corollary7.46 additionally uses general strong/modular Calderon transference and bounded-class polynomial convergence, including its still-unformalized published-theorem/cutoff/PNT/Abel/prime-power normalization bridges. Own unbounded Orlicz/L1 density convergence and identification of both limits are proved. These Prop-valued independent inputs are unproved theorem parameters, not new Lean mathematical axioms. Earlier Theorems1.1/1.3 and Propositions4.19/6.21 retain their separate recorded inputs; older ordinary global/local stopping hypotheses are not consumed by this new ordinary IW route. Theorem1.5(i) uses only the precise general split-polynomial Weil, fixed-progression prime-frequency PNT, original LaVictoire weak-maximal-failure, Sawyer and Conze inputs. Their existence and exact published-to-Lean convention bridges remain unproved. The optional quoted general GK input has a precise interface and checked joint Poisson application, but is not consumed by badness. All current-paper arithmetic, moment, limit, frequency and persistence deductions are proved.

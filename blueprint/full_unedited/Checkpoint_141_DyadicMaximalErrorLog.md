# Checkpoint 141: The conditional logarithmic dyadic maximal error estimate

The quantitative maximal error estimate is expressed in the manuscript's arithmetic-scale logarithm. Lean proves (J+1)^(1-(A+2))<=(1+log(2^J))^(-A) for every A>=0, including J=0.

Choosing s=A+2 in the full countable maximal bound gives a fixed positive constant C_A=2*dyadicErrorConstant(A+2) and the actual all-input estimate

    norm(sup_j |E_(2^(J+j)) f|)_2
      <= C_A*Q^(-1/2)*(1+log(2^J))^(-A)*norm(f)_2.

The Q range is imposed only at the starting scale and propagated rigorously. Character, coefficient and beta data may vary between scales, but the raw progression-prefix estimate uses one set of data throughout each scale's real endpoint interval. All external estimates remain explicit hypotheses.

This completes the conditional global approximation error and its dyadic maximal tail for the genuine circle model. The stronger printed Lemma 6.5, complete exceptional/source correspondence and the separate sharp low/high/multifrequency estimates remain open. Theorem 1.1 is not proved.


## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| DyadicMaximalErrorLog.lean | 3 |

- `dyadic_tail_power_log_bound`
- `maximalCircleErrorConstant_pos`
- `dyadicCircleError_maximal_log_rate`

<!-- checkpoint-verification -->

## Verification

All 208 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 3733-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 1090 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 210 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. Published Ren and Ghosh quadratic exponential-sum estimates, when consumed, remain displayed raw theorem hypotheses; the progression-prefix estimate also remains an explicit unproved input. No own-paper analytic conclusion is assumed.

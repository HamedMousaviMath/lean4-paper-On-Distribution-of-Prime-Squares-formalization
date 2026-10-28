# Checkpoint 129: Absolute summability and quantitative tails of operator norms

An arbitrary family of actual bounded l2 operators with a fixed power decay norm(T_j)<=K*(j+1)^(-s), s>=2, has a summable norm tail. Lean proves both norm summability and convergence of the operator series in the Banach space of continuous linear maps.

The exact quantitative tail is

    sum_j norm(T_(J+j)) <= 2*K*(J+1)^(1-s).

The estimate follows from the checked weighted scalar series and applies to every natural starting exponent. This is the summability mechanism for the actual dyadic error family, not an assumed maximal theorem. The actual decay bound from the conditional global approximation will be supplied at the later application.


## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| OperatorDecaySeries.lean | 3 |

- `operator_norm_shift_summable`
- `operator_norm_shift_tsum_bound`
- `operator_shift_summable`

<!-- checkpoint-verification -->

## Verification

All 196 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 3721-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 1060 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 198 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. Published Ren and Ghosh quadratic exponential-sum estimates, when consumed, remain displayed raw theorem hypotheses; the progression-prefix estimate also remains an explicit unproved input. No own-paper analytic conclusion is assumed.

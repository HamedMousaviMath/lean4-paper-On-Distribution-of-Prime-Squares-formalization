# Checkpoint 140: The genuine countable maximal error with a power tail

The genuine countable maximal function of the actual dyadic circle-error operators is now realized as a real l2 vector for every complex l2 input. Lean proves

    norm(sup_j |E_(2^(J+j)) f|)_2
      <= 2*dyadicErrorConstant(s)*Q^(-1/2)*(J+1)^(1-s)*norm(f)_2,

for s>=2, under the explicit scale-wise analytic inputs and the Q condition at the starting scale. There is one uniform arithmetic threshold before all J, Q and data. The supremum ranges over the entire infinite tail, and its coordinate equality is exact at every integer.

This is the maximal error component of the approximation argument. It does not provide the separate high-operator multifrequency bound or the low-kernel bound.


## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| DyadicMaximalErrorPower.lean | 1 |

- `dyadicCircleError_maximal_power`

<!-- checkpoint-verification -->

## Verification

All 207 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 3732-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 1087 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 209 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. Published Ren and Ghosh quadratic exponential-sum estimates, when consumed, remain displayed raw theorem hypotheses; the progression-prefix estimate also remains an explicit unproved input. No own-paper analytic conclusion is assumed.

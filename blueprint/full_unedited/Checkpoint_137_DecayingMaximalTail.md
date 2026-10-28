# Checkpoint 137: A quantitative countable maximal tail from power decay

The general countable maximal theorem is combined with the quantitative power-decay tail. If norm(T_(J+j))<=K*(J+j+1)^(-s) with K>=0 and s>=2, Lean constructs the actual maximal l2 function and proves

    norm(sup_j |T_(J+j) f|)_2 <= 2*K*(J+1)^(1-s)*norm(f)_2.

A positive l2 majorant with the same norm bound is also constructed and proved to dominate every output on the tail. Both statements are valid for all complex l2 inputs and all natural starting exponents. No finite truncation or extra maximal assumption is present.


## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| DecayingMaximalTail.lean | 2 |

- `decaying_operator_maximal_tail`
- `decaying_operator_maximal_tail_majorant`

<!-- checkpoint-verification -->

## Verification

All 204 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 3729-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 1082 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 206 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. Published Ren and Ghosh quadratic exponential-sum estimates, when consumed, remain displayed raw theorem hypotheses; the progression-prefix estimate also remains an explicit unproved input. No own-paper analytic conclusion is assumed.

# Checkpoint 125: A finite reciprocal-square tail with exact telescoping

The quantitative series estimate needed for the dyadic error tail begins with a checked telescoping inequality:

    1/(j+1)^2 <= 2*(1/(j+1)-1/(j+2)).

Lean proves the exact sum of the reciprocal differences on every integer interval [J,K), including the empty interval. It follows that the sum of 1/(j+1)^2 on that interval is at most 2/(J+1). This holds for all natural endpoints, with no hidden J>0 condition.

The estimates are elementary finite real inequalities. They will provide an explicit infinite-tail bound rather than relying only on qualitative convergence of a p-series.


## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| ReciprocalSquareFiniteTail.lean | 3 |

- `reciprocal_square_step`
- `reciprocal_step_sum`
- `reciprocal_square_finite_tail`

<!-- checkpoint-verification -->

## Verification

All 192 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 3717-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 1050 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 194 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. Published Ren and Ghosh quadratic exponential-sum estimates, when consumed, remain displayed raw theorem hypotheses; the progression-prefix estimate also remains an explicit unproved input. No own-paper analytic conclusion is assumed.

# Checkpoint 765: Complete the actual high maximum for changing class-indexed exceptional characters

The full actual high operator now has a countable dyadic maximal majorant for a class-indexed family of fixed quadratic characters, allowing arbitrary character changes between times, arbitrary active/inactive selectors, and arbitrary beta and denominator-radius sequences in their stated ranges. The only class condition is 2^i <= q_i. The proof uses the exact ordinary-minus-exceptional symbol identity, the sharp ordinary majorant, each fixed-character majorant, and the retained summable conductor decay. Linear summation over occupied classes already converges, so no unproved class square-function estimate is needed. The Q rate remains Q^(-1/2) exp(G(log Q)) (1+log Q)^3, uniformly over starting scales. The next step proves the class parametrization from a precise independent Page input rather than assuming it for the source family.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| SharpChangingCharacterMaximum.lean | 1 |

- `sharpChangingCharacter_maximum`

<!-- checkpoint-verification -->

## Verification

All 832 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4439-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2077 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 834 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results under their paper hypotheses remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. In addition, Lemma 3.21 and BOTH conclusions of Theorem 1.1 are complete checked implications under their explicit independent deep inputs. The PNT limits are used in the sharp Gauss/high bound; an imported PNT bridge is not integrated. The whole paper, the full maximal clauses of Proposition 4.19/6.21 and the later headline applications remain unfinished. See docs/THEOREM_1_1_EXTERNAL_INPUTS.md. PNT limits, raw compatible progression/Ren/Ghosh data, and the independent square decomposition remain explicit hypotheses. The smooth multifrequency boundary is only for later maximal applications.

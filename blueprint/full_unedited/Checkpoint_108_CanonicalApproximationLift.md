# Checkpoint 108: Canonical rational centers for an arbitrary selected approximation

Any rational approximation r is normalized to its exact fractional part, a canonical rational in [0,1). Its reduced denominator is unchanged by this normalization, using Mathlib's proved rational-floor theorem. The frequency offset is exactly rewritten as an integer lift of that canonical center:

    xi-r = xi-floor(r)-fract(r).

Lean proves that if den(r)<=R with R>=0, then fract(r) belongs to the exact finite sourceRationalCenters(R). The cast of the rational fractional part is explicit, avoiding an implicit change from rational to real floor operations.

This is the arithmetic bridge allowing a newly selected rational, whose numerator may fall outside the canonical interval, to be tested against all lifted source major arcs. It uses no prime-distribution or exponential-sum input.


## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| CanonicalApproximationLift.lean | 3 |

- `ratFract_canonical`
- `rational_offset_canonical_lift`
- `ratFract_mem_sourceRationalCenters`

<!-- checkpoint-verification -->

## Verification

All 175 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 3697-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 1007 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 177 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. Published Ren and Ghosh quadratic exponential-sum estimates, when consumed, remain displayed raw theorem hypotheses; the progression-prefix estimate also remains an explicit unproved input. No own-paper analytic conclusion is assumed.

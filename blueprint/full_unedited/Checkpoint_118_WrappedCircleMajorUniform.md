# Checkpoint 118: The uniform error bound on all lifted major arcs

The actual continuous circle error is exactly unchanged when an integer is added to a real representative. Lean proves this from the quotient identity rather than asserting periodicity of the underlying real oscillatory integral.

The conditional major-arc uniform theorem is then extended to any lifted major arc, with arbitrary integer k and condition |xi+k-r0|<=R/(den(r0)*N^2). Its conclusion concerns the original circle point xi. The same uniform N threshold, all-Q range and raw progression-prefix hypothesis are retained, and shifted copies of the denominator-one center are included.

This is the boundary-compatible major branch used by the global major/minor case split. No outside-arc or minor conclusion is assumed, and no new deep input is introduced.


## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| WrappedCircleMajorUniform.lean | 2 |

- `circleMajorArcError_integer_shift`
- `circleMajorArcError_major_lift_uniform`

<!-- checkpoint-verification -->

## Verification

All 185 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 3707-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 1032 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 187 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. Published Ren and Ghosh quadratic exponential-sum estimates, when consumed, remain displayed raw theorem hypotheses; the progression-prefix estimate also remains an explicit unproved input. No own-paper analytic conclusion is assumed.

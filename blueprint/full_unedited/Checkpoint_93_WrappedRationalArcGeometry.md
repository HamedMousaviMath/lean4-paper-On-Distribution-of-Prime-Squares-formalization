# Checkpoint 93: Rational arc geometry with every integer lift

This checkpoint proves rational-arc geometry on the circle while retaining every integer lift. Two different canonical center/lift pairs with denominators at most D are separated by at least 1/D^2. The proof treats distinct reduced rationals and distinct lifts of the same rational separately. Consequently two arcs of common radius delta with 2*delta<1/D^2 cannot meet unless both their centers and integer lifts agree.

For the manuscript's major-arc widths R/(q*N^2), the condition 2*R^3<N^2 gives uniqueness of the center/lift pair. If a frequency is on the major arc of r0, every distinct center or nonzero integer shift is strictly outside its own major arc. In particular, shifted copies of r0 itself are not omitted. The same argument proves uniqueness for the actual dyadic cutoff at scales s>=2. The earlier low-scale overlap bound remains applicable at the smaller scales; no uniqueness claim is made there.

The exact quotient identity says that adding any integer to a real representative gives the same point of PrimeCircle. Together these results cover the wrap across zero and one without assuming that the real-variable oscillatory integral is periodic. The proofs use only finite rational arithmetic, inequalities and the circle quotient; no progression estimate or minor-arc conclusion is assumed.


## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| WrappedRationalArcGeometry.lean | 6 |

- `primeCircle_coe_integer_shift`
- `canonicalLift_den_separation`
- `canonicalLift_small_arc_unique`
- `canonicalLift_major_arc_unique`
- `canonicalLift_other_outside`
- `cutoffScale_wrapped_unique`

<!-- checkpoint-verification -->

## Verification

All 160 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 3679-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 953 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 162 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. The already displayed raw progression-prefix estimate is consumed as a theorem hypothesis; it remains unproved. No new external analytic estimate or own-paper lemma is assumed.

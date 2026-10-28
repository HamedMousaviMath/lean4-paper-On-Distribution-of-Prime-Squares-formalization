# Checkpoint 112: The small-denominator Ren branch at the actual source scale

The raw Ren consuming theorem is combined with the proved fourth-power scale absorption. The actual annular multiplier is bounded by renSourceConstant(C)*(log(N/2))^c*R^(-5/12), provided N>=4, R>=1, R^4<=N/2, the selected denominator q<=sqrt(N/2), the balanced approximation precision holds, and its effective denominator is at least R/4.

The constant is the explicit product (C*renDivisorConstant/2)*renGeometryConstant; its nonnegativity is proved for C>=0. All divisor and logarithmic factors remain accounted for. The supplied Ren inequality involves the actual annular exponential sum at the same xi and theta as the chosen approximation.

This is the small-denominator analytic branch of the complementary argument. The deep raw estimate is explicit; the paper's own minor-arc conclusion is not assumed. The rational selection and outside-arc geometry will supply the remaining geometric hypotheses in the subsequent assembly.


## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| AnnularRenScaleBound.lean | 2 |

- `renSourceConstant_nonneg`
- `annularMangoldt_Ren_scale_bound`

<!-- checkpoint-verification -->

## Verification

All 179 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 3701-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 1017 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 181 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. Published Ren and Ghosh quadratic exponential-sum estimates, when consumed, remain displayed raw theorem hypotheses; the progression-prefix estimate also remains an explicit unproved input. No own-paper analytic conclusion is assumed.

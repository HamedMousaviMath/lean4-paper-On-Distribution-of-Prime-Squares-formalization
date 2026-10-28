# Checkpoint 95: Conditional major-arc approximation for the genuine circle model

This checkpoint transfers the progression-prefix major-arc estimate to the actual continuous circle error. It does not replace the circle model by its unperiodized real-variable counterpart. The old real-model error is combined with four additional integer shifts, obtained from the exact five-shift identity proved in checkpoint 94.

If xi is on the major arc of a canonical center r0 with denominator at most R, the separation condition 2*R^3<N^2 shows that every nonzero shift is outside every center's own major arc, including the shifted copies of r0. Their combined norm is at most four real-model tail budgets. The zero-shift error already contributes at most the inverse-fifth progression error plus one such tail. Thus the actual circle error is bounded by the common circleApproxBudget(C,R). The proof also establishes that the chosen lifted representative lies in [-1,2], so the finite-shift formula applies without an extra hypothesis.

The explicit inputs include N>=2, R>=1, 0<beta<=1, coefficient norms at most one, 2*R^3<N^2, 2*R^4<=N^2, log R<=log N, R^5*log N<=sqrt N and 7*log R<=c*sqrt(log N). The sole unproved distribution input is the displayed inequality for progressionMangoldtPrefix on the whole positive real interval [N/2,N], with error N*C*exp(-c*sqrt(log N)); the same character/coefficient/beta data must work throughout this interval. No approximation conclusion from the manuscript is assumed.

For the exact sourceRationalCenters(R) with R=sourceMajorArcScale(N,Q), the uniform theorem supplies one N threshold, independent of Q and the permitted exceptional data, giving

    norm(circle error) <= 2^A*Q^(-1/2)*(1+log N)^(-A).

Here C>=0, c>0, A>=0, Q>=1 and log Q <= (min(c/7,1)/8)*sqrt(log N). Canonicality and denominator bounds come from the exact membership theorem of checkpoint 92. Arcs crossing the circle boundary are handled by choosing their integer-shifted real representative; checkpoint 93 proves that its circle point is unchanged.

This completes this conditional major-arc branch for the actual periodized model. It is not the global approximation Lemma 6.9: the intermediate and larger denominator branches, and the full source exceptional-data correspondence, cannot be silently inferred. No LaTeX correction is prescribed by these proofs.


## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| PeriodizedMajorArcError.lean | 4 |

- `majorArc_representative_range`
- `realModelTailBudget_nonneg`
- `circleMajorArcError_from_prefix`
- `circleMajorArcError_uniform_log_rate`

<!-- checkpoint-verification -->

## Verification

All 162 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 3681-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 965 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 164 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. The already displayed raw progression-prefix estimate is consumed as a theorem hypothesis; it remains unproved. No new external analytic estimate or own-paper lemma is assumed.

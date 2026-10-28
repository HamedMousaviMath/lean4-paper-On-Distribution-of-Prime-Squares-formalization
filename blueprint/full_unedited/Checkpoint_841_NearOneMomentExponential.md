# Checkpoint 841: Exact exponential dependence on p minus one in the gauge moment

The scalar moment has the exact near-L1 exponential dependence displayed in c:orlicz-p. For C,C0>=1 and every 1<p<=2, Lean proves actual integrability on (1/C0,infinity) and bounds the integral of Psi_C(u)u^(-p-1) by exp(K(C,C0)/(p-1) log(exp(1)/(p-1))). The constant is explicit and quantified before p. The proof includes the lower cutoff, reciprocal power, prefactor absorption, and all p in the stated range. This is an unconditional scalar theorem. It does not assume or declare proved the operator modular estimate, its layer-cake norm implication, or the final ergodic assertion.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| NearOneMomentExponential.lean | 5 |

- `nearOne_log_reciprocal_bounds`
- `nearOneMoment_prefactor_one_le`
- `nearOneMomentConstant_pos`
- `nearOneGaugeMoment_exponential`
- `nearOneGaugeMoment_source_p`

<!-- checkpoint-verification -->

## Verification

All 908 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4515-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2461 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 910 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed source results under their paper hypotheses remain unchanged. Lemma 3.21, both conclusions of Theorems 1.1 and 1.3, all displayed clauses of Proposition 4.19 and both clauses of Proposition 6.21 are complete checked implications under their separately recorded independent deep inputs. The square-sign reflection is proved. Theorem 1.3 has actual finite sparse families, disjoint major subsets and the literal full all-cutoff maximum. The three general Section5 auxiliary statements remain partial, and the later Orlicz/ergodic/sieve applications remain unfinished. Proposition 4.19 consumes PrimeAsymptoticInputs, the refined PagePrimeSquareDistributionInputs c, RawPageUniquenessInput c and SmoothCircleBourgainInput C. These are independent raw analytic/data hypotheses, not own-paper operator conclusions or new Lean axioms. Theorem 1.1 retains its separately recorded older fixed-scale inputs and independent ordinary-square global decomposition; reflection is proved. Sparse applications additionally record OrdinarySquareStoppingInput CS and IndependentPrimeMaximalInput as explicit independent analytic boundaries. Their existence and the exact normalization/support/sign adaptations remain unproved; neither predicate contains this paper's endpoint or sparse conclusion.

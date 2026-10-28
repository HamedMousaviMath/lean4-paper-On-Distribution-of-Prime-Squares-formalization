# Checkpoint 839: Actual improper Orlicz moment and quantitative power integral

The actual improper gauge moment in c:orlicz-p is now controlled. Lean proves a global power majorant for Psi_C(u) on every interval u>=a>0, with an explicit constant containing exp(K(C)/(p-1) log(exp(1)/(p-1))). It proves actual integrability of Psi_C(u) u^(-p-1) over (a,infinity), and bounds its integral by an explicitly integrated power. This uses the checked literal gauge, continuity and Bochner improper integrals, and never replaces a divergent totalized integral by a number. The operator layer-cake and actual restricted arithmetic estimate remain separate obligations; this scalar result alone does not close c:orlicz-p.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| NearOneGaugeMoment.lean | 5 |

- `nearOnePowerConstant_pos`
- `nearOnePsi_power_majorant`
- `nearOneGaugeMoment_majorant`
- `nearOneGaugeMoment_integrable`
- `nearOneGaugeMoment_bound`

<!-- checkpoint-verification -->

## Verification

All 906 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4513-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2446 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 908 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed source results under their paper hypotheses remain unchanged. Lemma 3.21, both conclusions of Theorems 1.1 and 1.3, all displayed clauses of Proposition 4.19 and both clauses of Proposition 6.21 are complete checked implications under their separately recorded independent deep inputs. The square-sign reflection is proved. Theorem 1.3 has actual finite sparse families, disjoint major subsets and the literal full all-cutoff maximum. The three general Section5 auxiliary statements remain partial, and the later Orlicz/ergodic/sieve applications remain unfinished. Proposition 4.19 consumes PrimeAsymptoticInputs, the refined PagePrimeSquareDistributionInputs c, RawPageUniquenessInput c and SmoothCircleBourgainInput C. These are independent raw analytic/data hypotheses, not own-paper operator conclusions or new Lean axioms. Theorem 1.1 retains its separately recorded older fixed-scale inputs and independent ordinary-square global decomposition; reflection is proved. Sparse applications additionally record OrdinarySquareStoppingInput CS and IndependentPrimeMaximalInput as explicit independent analytic boundaries. Their existence and the exact normalization/support/sign adaptations remain unproved; neither predicate contains this paper's endpoint or sparse conclusion.

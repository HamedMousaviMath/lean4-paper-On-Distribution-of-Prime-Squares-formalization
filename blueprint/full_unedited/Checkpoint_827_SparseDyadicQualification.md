# Checkpoint 827: Check and document the required dyadic scope of the abstract recursion

Proves a concrete positive compactly supported convolution counterexample showing why the abstract recursion lemma must specify a dyadic maximum when its local hypothesis tests only dyadic stopping values. The kernel is zero at every dyadic index and equals the identity at N=3; all local dyadic pairings vanish but the unrestricted maximum is at least one on singleton test sets. Saves a proposed statement qualification for source Lemma 5.10 (l:sparserecursion) and a precise all-cutoff reduction paragraph for Theorem 1.3. These are proposed only, not applied to the current manuscript. The actual prime-square all-cutoff comparison and both sparse conclusions are already proved separately, so no new hypothesis is added to them.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| SparseDyadicQualification.lean | 7 |

- `two_pow_ne_three`
- `sparseNonDyadicKernel_positive`
- `sparseNonDyadicKernel_support`
- `sparseNonDyadicKernel_dyadic_zero`
- `sparseNonDyadic_local_pairing_zero`
- `sparseNonDyadic_full_pairing_one`
- `sparseNonDyadic_maximum_positive`

<!-- checkpoint-verification -->

## Verification

All 894 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4501-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2363 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 896 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results under their paper hypotheses remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. Lemma 3.21, both conclusions of Theorem 1.1, all displayed clauses of Proposition 4.19 and both clauses of Proposition 6.21 are complete checked implications under their separately recorded independent deep inputs. The square-sign reflection is proved. The whole paper, the stronger printed auxiliary lemmas and the later sparse/ergodic/sieve applications remain unfinished. Proposition 4.19 consumes PrimeAsymptoticInputs, the refined PagePrimeSquareDistributionInputs c, RawPageUniquenessInput c and SmoothCircleBourgainInput C. These are independent raw analytic/data hypotheses, not own-paper operator conclusions or new Lean axioms. Theorem 1.1 retains its separately recorded older fixed-scale inputs and independent ordinary-square global decomposition; reflection is proved. Sparse applications additionally record OrdinarySquareStoppingInput CS and IndependentPrimeMaximalInput as explicit independent analytic boundaries. Their existence and the exact normalization/support/sign adaptations remain unproved; neither predicate contains this paper's endpoint or sparse conclusion.

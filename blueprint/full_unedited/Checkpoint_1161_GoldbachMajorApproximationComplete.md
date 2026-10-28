# Checkpoint 1161: Complete source major-arc approximation under ordinary SW and BV

The full source major-arc approximation, stable label l:majorapproximation9, is now a complete Lean implication under only RawPrimeSiegelWalfiszInput and RawPrimeBombieriVinogradovInput. These independent hypotheses concern ordinary unweighted prime progression counts; neither contains an oscillatory model, the paper coefficient family or its endpoint conclusion. Their analytic proofs remain external.

For every A>0, C≥0 and delta>0, the theorem selects B0, a positive error constant and a sufficiently large integer scale before all source data. It covers every B≥B0, every strict printed L0 and V range, every reduced progression residue and bounded complex coefficient, every real2≤U≤N and every realW≥2. In particular it covers the paper's W≤N² range. The sum over all natural n<N² is exactly the source weighted sum of model-replacement integrals on the actual circle major arcs, bounded by K N⁴(log N)^(-A).

The actual Fourier signs, rational centres, normalized measure, strict prime cutoff, nonunit primes, Upsilon coefficient, genuine Euclidean integrals and measurable circle models are all supplied. SW uses exponent(A+6)/2; BV uses(A+3C)/2. Restricted Bessel, the measure bound8R³/N² and the previously proved progression-energy bound give the explicit final constant2(8 KE²/(log2)²+KP²·256/log2).

A small proof correction is required: W≤N²/ell does not make ell*t<N² automatic at equality. The endpoint and primes dividingq contribute at most1+q to each individual error. All these finite errors are proved absorbed uniformly. The separate replacement files retain the lemma statement and equation labels and give the checked unweighted fixed-q fibre route. The selected manuscript is unchanged.

This closes one paper-level claim after review of its exact source statement and quantifiers. The ledger is now13 proved,26 complete conditional implications,1 quoted external theorem and14 open. The full circle-method approximation l:circmethod still requires completion/arithmetic evaluation and the smooth Euclidean-cutoff stage. Section11 and the headline Goldbach theorem remain open.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachMajorApproximationComplete.lean | 1 |

- `goldbach_major_approximation_complete`

<!-- checkpoint-verification -->

## Verification

All 1228 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 5019-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 3846 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1230 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; the Section10/11 analytic and sieve estimates remain open internal obligations. The rational smooth multifrequency theorem with circle transference remains an explicit independent compound hypothesis. The classical primitive sum-of-two-squares criterion is an additional explicit independent arithmetic hypothesis for Section9 reductions; it contains no own-paper conclusion and is not declared as a Lean axiom.

# Checkpoint 1202: Actual quantitative added-modulus major-family Bessel estimate

The actual added-modulus Fourier family now satisfies the quantitative Bessel estimate: its squared coefficient sum over any finite output set is at most K N^4(log N)^4/sqrt(R). The constant is chosen before N, the arithmetic family, coefficients, cutoffs, upper denominator bound and output set.

The proof applies the exact actual integrands, their seed-derived support, the rational disjointness theorem, the proved envelope energies and the complete primitive-numerator denominator sum. It retains the elementary geometric conditions epsilon=R/(4N²)<1/2 and2epsilon<Y^(-2); these will be discharged for the printed Y=N/(100sqrt(R)). The finite rational set may be any subset of the added denominators, so the source R-smooth restriction is included.

This is the full analytic estimate for adding the intermediate smooth moduli, with no independent completion or large-sieve hypothesis. The remaining work is source parameter geometry and the sharp-to-smoothed small-modulus comparison, followed by final assembly.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachAddedMajorBessel.lean | 1 |

- `goldbach_smooth_added_major_bessel`

<!-- checkpoint-verification -->

## Verification

All 1269 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 5062-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 4034 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1271 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; the Section10/11 analytic and sieve estimates remain open internal obligations. The rational smooth multifrequency theorem with circle transference remains an explicit independent compound hypothesis. The classical primitive sum-of-two-squares criterion is an additional explicit independent arithmetic hypothesis for Section9 reductions; it contains no own-paper conclusion and is not declared as a Lean axiom.

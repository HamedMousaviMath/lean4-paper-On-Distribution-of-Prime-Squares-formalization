# Checkpoint 1128: Finite Abel summation and logarithmic unweighting

A finite Abel-summation norm inequality is now proved directly from Mathlib's exact summation-by-parts identity. For nonnegative decreasing real weights a_i and complex coefficients z_i whose actual partial sums have norm at most B, the weighted sum over range(n) has norm at most B*a_0. The proof includes n=0, the boundary term, the variation terms and their exact telescoping total. It is a proved inequality, not an additional summation-by-parts hypothesis.

The logarithmic removal weight is the actual function 1/log(max(2,n)). Its nonnegativity, monotonicity, initial value1/log2 and equality to1/log n at every n>=2 are all proved. Clipping at2 is only a finite-index convention: von-Mangoldt weights at0 and1 vanish. It prevents an invalid monotonicity assertion across log1=0.

These five supporting theorems supply the discrete logarithmic unweighting step. The next step identifies the unweighted Mangoldt sum with the actual prime sum up to the endpoint, apart from the already bounded higher prime-power contribution. The full Goldbach minor, major and sieve estimates are not newly claimed proved. No new independent deep input or manuscript replacement is introduced.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachFiniteAbel.lean | 5 |

- `goldbach_finite_abel_bound`
- `goldbachLogRemovalWeight_nonneg`
- `goldbachLogRemovalWeight_antitone`
- `goldbachLogRemovalWeight_zero`
- `goldbachLogRemovalWeight_of_two_le`

<!-- checkpoint-verification -->

## Verification

All 1195 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4986-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 3685 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1197 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; the Section10/11 analytic and sieve estimates remain open internal obligations. The rational smooth multifrequency theorem with circle transference remains an explicit independent compound hypothesis. The classical primitive sum-of-two-squares criterion is an additional explicit independent arithmetic hypothesis for Section9 reductions; it contains no own-paper conclusion and is not declared as a Lean axiom.

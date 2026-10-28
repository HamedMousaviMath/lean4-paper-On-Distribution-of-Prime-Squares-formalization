# Checkpoint 1130: Exact Mangoldt halving reconstruction and uniform partial sums

The halving step is now proved by strong induction, with the exact integer floor at every scale. A bound on F(m)-F(floor(m/2)) above a real threshold H, together with a bound for the actual small partial sums, gives |F(m)|<=2 B m+E. The proof includes zero and odd scales and uses 2 floor(m/2)<=m; no unproved dyadic reconstruction is inserted.

For the genuine Mangoldt exponential sums, the half-scale identity is proved from the exact finite intervals. The positive Fourier phase is identified with the existing Ren convention. Its annular difference has norm exactly m times the actual normalized annular symbol. A crude small-scale bound |S_m|<=m log N is proved directly from the elementary pointwise von-Mangoldt/logarithm inequality, without PNT or a prime-counting hypothesis.

The terminal theorem assembles the uniform bound |S_m|<=2 B N+H log N for all m<=N from a common annular symbol bound B above H. These seven supporting theorems discharge the discrete reconstruction and all finite cutoff conventions. The common annular estimate will next be supplied by the existing raw Ren/Ghosh inputs using explicit rescaled complementary arcs. No new independent deep hypothesis or manuscript replacement is introduced.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachHalvingPartials.lean | 7 |

- `goldbach_halving_partial_bound`
- `goldbachMangoldtPrefix_halving`
- `goldbach_positive_quadratic_character`
- `goldbachMangoldtPrefix_annular_Ren`
- `goldbachMangoldtPrefix_annular_norm`
- `goldbachMangoldtPrefix_crude`
- `goldbach_mangoldt_partials_from_annular`

<!-- checkpoint-verification -->

## Verification

All 1197 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4988-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 3700 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1199 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; the Section10/11 analytic and sieve estimates remain open internal obligations. The rational smooth multifrequency theorem with circle transference remains an explicit independent compound hypothesis. The classical primitive sum-of-two-squares criterion is an additional explicit independent arithmetic hypothesis for Section9 reductions; it contains no own-paper conclusion and is not declared as a Lean axiom.

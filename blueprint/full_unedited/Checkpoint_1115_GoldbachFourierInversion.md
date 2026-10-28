# Checkpoint 1115: Exact unweighted Goldbach Fourier inversion and full-cutoff removal

The Section10 Fourier identity is now proved for the literal unweighted prime sums. Prime cutoffs have arbitrary real endpoints, and membership is exactly primality together with m<=U. The progression cutoff retains ell*t<N^2 and t congruent to a modulo k. Neither a coprimality assumption nor a distribution theorem is needed for this identity.

The positive exponential convention is Mathlib's fourier j on the period-one circle with Haar mass one. Character orthogonality is proved from the existing Fourier basis; the product of the actual prime-square and progression polynomials is expanded before integration. The coefficient at n is exactly the complex embedding of the finite number of ordered prime pairs, including all real endpoint conventions. This is equation e:fourierinversion9, not an assumed Fourier identity.

For positive ell and n<N^2, goldbach_full_cutoffs_redundant proves that U=N, W=N^2 and ell*t<N^2 impose no additional restriction on the untruncated prime-pair count. All finiteness bounds are deduced from m^2+ell*t=n. The terminal goldbach_full_fourier_inversion therefore identifies the full representation count itself with the circle integral.

Eight new supporting theorems are unconditional. No analytic minor/major estimate, sieve bound, external theorem or paper endpoint is assumed or proved by this checkpoint. Lemma l:circmethod and the headline Goldbach theorem remain open; the exact Fourier bridge is a proved prerequisite. The user reports applying the complete approximation proof and the three earlier sparse/wording/strict-approximation edits. Work proceeds with the selected reconciled source; no new manuscript upload or verification of the user's editor is claimed.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachFourierInversion.lean | 8 |

- `mem_goldbachPrimeCutoff`
- `mem_goldbachProgressionCutoff`
- `goldbach_finite_character_integral`
- `goldbachPrimeSquarePolynomial_mul`
- `goldbach_cutoff_fourier_inversion`
- `mem_goldbachCutoffPrimePairs`
- `goldbach_full_cutoffs_redundant`
- `goldbach_full_fourier_inversion`

<!-- checkpoint-verification -->

## Verification

All 1182 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4973-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 3617 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1184 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; the Section10/11 analytic and sieve estimates remain open internal obligations. The rational smooth multifrequency theorem with circle transference remains an explicit independent compound hypothesis. The classical primitive sum-of-two-squares criterion is an additional explicit independent arithmetic hypothesis for Section9 reductions; it contains no own-paper conclusion and is not declared as a Lean axiom.

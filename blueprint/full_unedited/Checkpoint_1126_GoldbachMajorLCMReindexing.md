# Checkpoint 1126: Major-arc lcm multiplicity and divisor-weighted error reindexing

The major-arc change from the modulus k to h=lcm(k,q) is now proved exactly. The fibre of k with lcm(k,q)=h is a subset of the actual divisors of h, hence contains at most tau(h) elements. No coprimality or guessed fibre multiplicity is imposed.

For every finite modulus set and nonnegative error function E, the sum of E(lcm(k,q)) is bounded by the sum of tau(h)E(h) over any interval covering all image moduli. The source tau(h)^2 version follows from an elementary natural-power inequality. The final theorem specializes this to complex progression errors bounded by R^2 E(lcm(k,q)), obtaining the exact weighted divisor-error sum used before the weighted Bombieri–Vinogradov input.

These five supporting theorems establish only the finite reindexing and multiplicity deductions. The actual progression error estimate, the weighted consequence of the general Bombieri–Vinogradov theorem and the full major approximation remain separate internal obligations. No new distribution theorem, own-paper estimate or mathematical axiom is assumed. The already completed progression energy and earlier source scopes are unchanged. No manuscript replacement is required.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachMajorLCMReindexing.lean | 5 |

- `goldbach_lcm_fibre_subset_divisors`
- `goldbach_lcm_fibre_card`
- `goldbach_lcm_weighted_sum`
- `goldbach_lcm_weighted_square_divisor_sum`
- `goldbach_major_progression_error_sum`

<!-- checkpoint-verification -->

## Verification

All 1193 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4984-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 3674 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1195 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; the Section10/11 analytic and sieve estimates remain open internal obligations. The rational smooth multifrequency theorem with circle transference remains an explicit independent compound hypothesis. The classical primitive sum-of-two-squares criterion is an additional explicit independent arithmetic hypothesis for Section9 reductions; it contains no own-paper conclusion and is not declared as a Lean axiom.

# Checkpoint 1172: Exact primitive progression cancellation and CRT bound

The actual progression exponential sum vanishes under a nontrivial square-zero translation preserving the progression. Such a translation is constructed whenever the divisor modulus and its complementary factor share a prime. The primitive additive frequency supplies the nontrivial phase, so the cancellation is exact.

In the coprime case, an explicit CRT unit permutation fixes the progression coordinate. The free coordinate gives a genuine Ramanujan sum at a unit, equal to the Mobius function. Consequently its norm is at most one. These primitive-frequency statements are proved directly from the source finite sums and the earlier elementary character identities, with no independent progression-sum estimate.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachPrimitiveProgression.lean | 3 |

- `goldbach_progression_exponential_zero_translation`
- `goldbach_progression_exponential_noncoprime`
- `goldbach_progression_exponential_coprime_norm`

<!-- checkpoint-verification -->

## Verification

All 1239 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 5032-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 3899 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1241 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; the Section10/11 analytic and sieve estimates remain open internal obligations. The rational smooth multifrequency theorem with circle transference remains an explicit independent compound hypothesis. The classical primitive sum-of-two-squares criterion is an additional explicit independent arithmetic hypothesis for Section9 reductions; it contains no own-paper conclusion and is not declared as a Lean axiom.

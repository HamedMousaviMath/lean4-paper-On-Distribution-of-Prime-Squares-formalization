# Checkpoint 1166: Exact coefficient identities and odd-prime gcd decay

Three exact identities are proved for the genuine arbitrary-multiplier coefficient: when q divides k, it is C_q(n-ell*b)/phi(q); when q is coprime to k and ell is a unit modulo q, it is mu(q) C_q(n)/phi(q)²; when q is coprime to k and ell vanishes modulo q, it is C_q(n)/phi(q). The unit case uses an actual permutation of the residue units, not an assumed invariance.

The existing exact odd-prime Cohen evaluation gives norm C_p(n)≤p+1. Splitting p|k, p|ell and p∤k*ell yields the full bound norm G_p(ell,k,n)≤8 gcd(p,k*ell)/p for every odd prime and arbitrary source parameters. The coefficient retains the actual Gauss/Upsilon normalizations. Bounds for arbitrary moduli and for the individual Upsilon sums, together with smoothing and smooth-modulus tails, remain open; no full source arithmetic lemma or completion is claimed.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachArithmeticPrime.lean | 5 |

- `goldbach_general_coefficient_of_dvd`
- `goldbach_general_coefficient_of_coprime_unit`
- `goldbach_general_coefficient_of_coprime_zero`
- `goldbach_odd_prime_cohen_norm`
- `goldbach_general_coefficient_odd_prime_bound`

<!-- checkpoint-verification -->

## Verification

All 1233 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 5026-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 3873 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1235 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; the Section10/11 analytic and sieve estimates remain open internal obligations. The rational smooth multifrequency theorem with circle transference remains an explicit independent compound hypothesis. The classical primitive sum-of-two-squares criterion is an additional explicit independent arithmetic hypothesis for Section9 reductions; it contains no own-paper conclusion and is not declared as a Lean axiom.

# Checkpoint 1144: Exact Upsilon normalization from compatible lcm residues

The compatible lcm residues are proved to map bijectively onto the actual unit residues modulo q satisfying the gcd compatibility condition. The map preserves every additive character. The finite character sum divided by phi(lcm(k,q)) is therefore exactly Upsilon(q,k,a,-alpha)/phi(k), with the source negative argument and both totient factors. Shared-prime cases are included through generalized CRT, not excluded. No analytic distribution hypothesis is used in this arithmetic identity.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachMajorUpsilonIdentity.lean | 6 |

- `goldbach_reduction_val`
- `goldbach_major_residue_image`
- `goldbach_major_castq_injective`
- `goldbach_major_residue_sum`
- `goldbach_major_compatibility_character`
- `goldbach_major_upsilon_identity`

<!-- checkpoint-verification -->

## Verification

All 1211 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 5002-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 3767 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1213 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; the Section10/11 analytic and sieve estimates remain open internal obligations. The rational smooth multifrequency theorem with circle transference remains an explicit independent compound hypothesis. The classical primitive sum-of-two-squares criterion is an additional explicit independent arithmetic hypothesis for Section9 reductions; it contains no own-paper conclusion and is not declared as a Lean axiom.

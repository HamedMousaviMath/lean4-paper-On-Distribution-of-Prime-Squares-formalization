# Checkpoint 1217: Exact upper sieve progression sequence

Proved the exact upper divisibility-sequence count as an untruncated prime-square/progression count at modulus12d and argument n-1. The congruence equivalence is proved in both directions. The progression conditions force the prime-square variable to exceed3 and the other prime to be3 modulo4. The actual closed multiplier set is proved to supply ell=2v with v=3 modulo4 and coprime to6 once z>3. A valid coprime residue is chosen before all n. The actual arithmetic/singular main term plus circle-method remainder identity is exported, with the natural n-1 argument retained exactly.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachUpperSieveSequence.lean | 7 |

- `goldbach_upper_sieve_residue_iff`
- `goldbach_upper_prime_conditions`
- `goldbach_upper_sieve_sequence_count`
- `goldbach_prime_support_one_mod_four`
- `goldbach_closed_multiplier_residue_data`
- `goldbach_upper_sequence_fixed_residue`
- `goldbach_upper_sequence_circle_identity`

<!-- checkpoint-verification -->

## Verification

All 1284 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 5077-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 4102 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1286 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; all Section10 statements and the full circle-method implication are complete in the agreed conditional scope; Section11 remains open. The rational smooth multifrequency theorem with circle transference remains an explicit independent compound hypothesis. The classical primitive sum-of-two-squares criterion is an additional explicit independent arithmetic hypothesis for Section9 reductions; it contains no own-paper conclusion and is not declared as a Lean axiom.

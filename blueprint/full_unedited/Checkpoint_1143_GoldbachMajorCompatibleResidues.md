# Checkpoint 1143: Compatible lcm unit residues and generalized CRT

The reduced residue classes modulo lcm(k,q) compatible with the prescribed residue modulo k are actual finite sets of natural representatives. Their reduction modulo q is injective, so their cardinality is at most q. The generalized CRT constructs every class compatible modulo gcd(k,q), with exact representative bounds and both unit conditions. The converse compatibility and unit properties are proved. These facts retain shared prime factors of k and q; no coprime-moduli simplification is imposed.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachMajorCompatibleResidues.lean | 5 |

- `mem_goldbachMajorResidues`
- `goldbach_major_residues_modq_injective`
- `goldbach_major_residues_card`
- `goldbach_major_compatible_lift`
- `goldbach_major_residue_compatible`

<!-- checkpoint-verification -->

## Verification

All 1210 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 5001-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 3761 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1212 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; the Section10/11 analytic and sieve estimates remain open internal obligations. The rational smooth multifrequency theorem with circle transference remains an explicit independent compound hypothesis. The classical primitive sum-of-two-squares criterion is an additional explicit independent arithmetic hypothesis for Section9 reductions; it contains no own-paper conclusion and is not declared as a Lean axiom.

# Checkpoint 1119: Uniform simultaneous-congruence interval counting

The simultaneous-congruence interval count is proved with exact constants. For any finite subset F of [A,A+T) whose members are pairwise congruent modulo q, card(F)<=T/q+1, first with natural division and then with literal real division. The proof chooses the least member only in the nonempty case and injects t into (t-min(F))/q. It therefore does not presume a compatible residue class or a solution. The empty case is separate; zero lengths and even the formal zero modulus are included.

The actual simultaneous congruence set retains both residue conditions. For any two of its members, Mathlib's Nat.mod_lcm proves congruence modulo lcm(k1,k2). Specialization yields card <=T/lcm(k1,k2)+1 in natural and real forms. Neither CRT existence, coprimality of the moduli/residues nor a prime-distribution theorem is assumed. These four supporting theorems supply the exact interval-counting ingredient in the source diagonal estimate and equation e:wellsquare9.

The reciprocal-lcm logarithmic bound was already proved at1118. Their combination into the actual squared multiplicity and progression-energy estimate is the next internal task. No source hybrid estimate, major estimate, sieve bound or headline theorem is newly declared complete. No manuscript replacement is required.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachCongruenceCounting.lean | 4 |

- `goldbach_congruence_interval_card`
- `goldbach_congruence_interval_card_real`
- `goldbach_simultaneous_congruence_count`
- `goldbach_simultaneous_congruence_count_real`

<!-- checkpoint-verification -->

## Verification

All 1186 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4977-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 3642 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1188 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; the Section10/11 analytic and sieve estimates remain open internal obligations. The rational smooth multifrequency theorem with circle transference remains an explicit independent compound hypothesis. The classical primitive sum-of-two-squares criterion is an additional explicit independent arithmetic hypothesis for Section9 reductions; it contains no own-paper conclusion and is not declared as a Lean axiom.

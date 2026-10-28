# Checkpoint 1120: Exact squared congruence-multiplicity estimate

The actual congruence multiplicity w(t), defined as the cardinality of moduli k satisfying t congruent to a(k) modulo k, is formalized. Its finite square is expanded exactly into the sum over pairs of moduli of the cardinality of their simultaneous-congruence set. No mean-square or counting estimate is assumed in this identity.

The interval count proved at1119 yields sum_{A<=t<A+T} w(t)^2 <= T sum_{k,j in K} 1/lcm(k,j)+card(K)^2. A proved subset version of the reciprocal-lcm bound therefore gives T H_M^3+card(K)^2 whenever K is any subset of [1,M]. This retains the local modulus count rather than replacing it by the global bound M^2, which would be too costly after summing over ell.

For every real V>=1, the literal strict source cutoff 0<k<V gives the exact bound T(1+log V)^3+V^2. This is a complete direct proof of the elementary squared-multiplicity estimate used in e:wellsquare9, with arbitrary residues and all natural interval endpoints. There is no coprimality, compatibility, prime-distribution or own-paper analytic assumption. The five new supporting theorems are unconditional arithmetic/finite-sum deductions. The full source progression-energy and hybrid minor estimates remain open.

A possible efficient route to the global energy uses grouping at each prime-product frequency and its number of distinct prime divisors. It will be checked explicitly before replacing the source dyadic bookkeeping in the formal proof. No manuscript edit is currently required.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachCongruenceMultiplicity.lean | 5 |

- `goldbach_congruence_square_identity`
- `goldbach_congruence_square_lcm_bound`
- `goldbach_reciprocal_lcm_subset`
- `goldbach_congruence_square_harmonic_bound`
- `goldbach_congruence_square_strict_real_cutoff`

<!-- checkpoint-verification -->

## Verification

All 1187 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4978-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 3647 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1189 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; the Section10/11 analytic and sieve estimates remain open internal obligations. The rational smooth multifrequency theorem with circle transference remains an explicit independent compound hypothesis. The classical primitive sum-of-two-squares criterion is an additional explicit independent arithmetic hypothesis for Section9 reductions; it contains no own-paper conclusion and is not declared as a Lean axiom.

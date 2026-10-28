# Checkpoint 1094: Actual Goldbach representation sets and uniform prime-divisor exception bounds

Introduced the actual finite prime-plus-prime-square representation sets, primitive good set, residue-class admissible set, sifted set and explicit exception envelope indexed by prime divisors of n-1. Proved that a shared prime divisor of r-1 and n-1 must equal the represented square prime, bounds the entire exceptional set by omega(n-1), and gives the full uniform O_epsilon(N^epsilon) error for n-1<=N^2. The coprimality removal used in the upper reduction is proved as well. For n>12 in the source residue class, every representation has square prime>3 and r congruent11 modulo24. These arithmetic statements have no new external theorem inputs. The numbered sieve reductions are not promoted before their remaining set inclusions are proved.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachFiniteRepresentations.lean | 11 |

- `mem_goldbachRepresentations`
- `goldbach_representation_unique_prime`
- `goldbach_shared_prime_eq`
- `goldbach_shared_divisor_exception`
- `goldbachDivisorExceptions_card`
- `goldbach_factor_coprime_of_not_exception`
- `goldbachSifted_antitone`
- `goldbach_prime_divisor_power_error`
- `goldbachDivisorExceptions_power_error`
- `goldbach_square_prime_large`
- `goldbach_representation_admissible`

<!-- checkpoint-verification -->

## Verification

All 1161 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4952-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 3519 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1163 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The current complete manuscript upload confirms the independent admissibility coefficient. The full generic sparse recursion is proved under its normal local hypothesis. The unchanged upload and a separate selected copy with the previously approved factor-four application restored are preserved. Two source statements remain partial: the original strong minor-arc clause and the broad standalone quantitative IW function classes. The full multifrequency lemma and denominator corollary, including measurable fixed symbols, are complete conditional implications. Section9 mapping is saved and its reductions are authorized; later circle-method and sieve conclusions remain internal proof obligations. The rational smooth multifrequency theorem together with circle transference is an explicit independent compound hypothesis; its existence is unproved. Its predicate contains no own-paper annular or truncated maximal conclusion. See docs/RATIONAL_MULTIFREQUENCY_BOUNDARY.md.

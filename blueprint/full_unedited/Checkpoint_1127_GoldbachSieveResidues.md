# Checkpoint 1127: Exact lower and upper sieve CRT residues and common product class

The literal lower and upper sieve residue choices in e:lowerresidue9 and e:upperresidue9 are now constructed in Lean using CRT and actual modular units. The helper for solving a*r=b modulo n constructs a bounded natural representative from a unit of ZMod n; it includes n=1. Congruence preserves the required coprimality by the actual gcd identity.

For every positive d coprime to6, a lower residue a<24d is constructed with a=11 mod24, a=1 modd and gcd(a,24d)=1. The source condition that all prime divisors of d exceed3 is separately proved to imply positivity and coprimality to6, so the source lower application is included; squarefreeness is not needed for this stronger arithmetic statement.

For ell=2v with gcd(v,6)=1 and positive d coprime to12ell, an upper residue a<12d is constructed with v*a=5 mod12, ell*a+1=0 modd and gcd(a,12d)=1. The second common residue b<12d is also constructed using only d, with b=10 mod12, b+1=0 modd and gcd(b,12d)=2. Every permitted upper residue satisfies ell*a=b mod12d. Thus the printed independence from ell and the exact gcd-two conclusion are proved, rather than inferred from examples.

All six supporting theorems are unconditional elementary arithmetic deductions. They do not assert the lower/upper sieve estimates, a sieve main-term lower bound, normalized integral positivity or the headline Goldbach theorem. The full progression-energy estimate is already proved at1124. The source hybrid minor still needs the actual weighted-annular to unweighted-prime-prefix bridge; major approximation/completion and the later analytic sieve work remain open. No new independent deep hypothesis or manuscript replacement is introduced.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachSieveResidues.lean | 6 |

- `goldbach_coprime_of_congruence`
- `goldbach_modular_linear_residue`
- `goldbach_lower_sieve_residue`
- `goldbach_lower_sieve_residue_from_support`
- `goldbach_upper_sieve_residue`
- `goldbach_upper_sieve_common_product_residue`

<!-- checkpoint-verification -->

## Verification

All 1194 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4985-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 3680 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1196 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; the Section10/11 analytic and sieve estimates remain open internal obligations. The rational smooth multifrequency theorem with circle transference remains an explicit independent compound hypothesis. The classical primitive sum-of-two-squares criterion is an additional explicit independent arithmetic hypothesis for Section9 reductions; it contains no own-paper conclusion and is not declared as a Lean axiom.

# Checkpoint 1220: Actual local Euler factors and prime adjunction

The exact progression coefficient is evaluated whenever \(q\mid\ell k\), rather than requiring \(q\mid k\). Reduction of units to \(\gcd(q,k)\), together with the normalized unit-fiber mass, gives
\[
 G_q(\ell,k,b,n)=\frac{C_q(n-\ell b)}{\phi(q)}.
\]
The proof starts from the already checked character coefficient and proves the finite averaging identity internally. In particular this handles the upper sieve at modulus8 even though its base progression modulus is12 and its multiplier is even.

For every prime, the actual unrestricted Euler factor, with multiplier invertible modulo that prime, is
\[
 1+G_p=\frac{p(p-1-\rho_p(n))}{(p-1)^2}.
\]
For a fixed progression unit it is \(p\rho_p(n-\ell b)/(p-1)\). When the multiplier vanishes modulo the prime, the common factor is \(p\rho_p(n)/(p-1)\), which may be zero. The actual unrestricted pair count also satisfies \(\#\mathrm{pairs}+\rho_p(n)=p-1\).

Under \(24\mid\ell k\) and \(n-\ell b\equiv1\pmod{24}\), the small-prime factors are exactly8 at2 and3 at3. Thus the original arithmetic factor is24 times the product over primes \(p>3\) with \(p\leq R\). Congruent progression residues give equal original coefficients and arithmetic factors.

Adjoining a prime \(p>3\), with \(p\nmid k\ell\), and imposing \(\ell b\equiv c\pmod p\), proves the exact normalized identity
\[
 \frac{G_R(\ell,kp,b,n)}{\phi(kp)}
 =\frac{G_R(\ell,k,b,n)}{\phi(k)}
 \begin{cases}
 \rho_p(n-c)/(p-1-\rho_p(n)),&p\leq R,\\
 1/(p-1),&p>R.
 \end{cases}
\]
Every other prime factor is proved unchanged. The proof multiplies local equalities and uses only the strictly positive unrestricted factor at the newly adjoined prime. It never divides by the complete base arithmetic factor, so common zero obstructions are retained correctly.

Scope: these are exact identities for the original finite character coefficients and Euler products, with no added deep inputs. The source local-density lemmas remain open at this saved milestone; the next milestone proves finite-prime assembly and the exact lower and upper CRT specializations.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachSieveConductor.lean | 2 |
| GoldbachSievePrimeFactors.lean | 4 |
| GoldbachSieveSmallFactors.lean | 4 |
| GoldbachSieveResidueFactors.lean | 4 |
| GoldbachSievePrimeAdjunction.lean | 3 |

- `goldbach_modular_multiplier_constant`
- `goldbach_general_coefficient_conductor`
- `goldbach_prime_unrestricted_factor`
- `goldbach_prime_fixed_factor`
- `goldbach_prime_zero_multiplier_factor`
- `goldbach_prime_unrestricted_count`
- `goldbach_two_factor_admissible`
- `goldbach_three_factor_admissible`
- `mem_goldbach_large_local_primes`
- `goldbach_arithmetic_factor_large_primes`
- `goldbach_general_coefficient_residue_congr`
- `goldbach_arithmetic_factor_coefficient_product`
- `goldbach_arithmetic_factor_residue_congr`
- `goldbach_prime_factor_unchanged`
- `goldbach_prime_local_density_ratio`
- `goldbach_arithmetic_factor_adjoin_prime`
- `goldbach_normalized_factor_adjoin_prime`

<!-- checkpoint-verification -->

## Verification

All 1293 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 5086-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 4141 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1295 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; all Section10 statements and the full circle-method implication are complete in the agreed conditional scope; Section11 remains open. The rational smooth multifrequency theorem with circle transference remains an explicit independent compound hypothesis. The classical primitive sum-of-two-squares criterion is an additional explicit independent arithmetic hypothesis for Section9 reductions; it contains no own-paper conclusion and is not declared as a Lean axiom.

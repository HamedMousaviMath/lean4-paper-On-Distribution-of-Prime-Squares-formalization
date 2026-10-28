# Checkpoint 1219: Actual root counts, density bounds and multiplicativity

The local root count is the actual finite number
\[
 \rho_p(a)=\#\{u\in(\mathbb Z/p\mathbb Z)^\times:u^2=a\}.
\]
Opening the prime Ramanujan sum proves the exact identity
\[
 C_p(a)=p\rho_p(a)-(p-1).
\]
The previously proved odd-prime Cohen evaluation then gives \(\rho_p(a)=2\) when its Legendre symbol is1 and0 otherwise. In particular \(0\leq\rho_p(a)\leq2\), with zero roots at the zero residue. The progression-restricted solution count is proved equal to \(\rho_p(n-\ell b)\); it is a cardinality identity for the actual pair set, not a replacement model.

The lower and upper candidate prime densities are defined with the source's inclusive cutoff \(p\leq R\). Their denominators are strictly positive for every prime \(p>3\). Both are nonnegative and bounded by \(2/(p-3)\), which is strictly below1 for \(p\geq7\). At5, a kernel-checked exhaustive calculation proves that either \(\rho_5(n)=0\), or \(\rho_5(n)=2\) and \(\rho_5(n-1)=0\). This proves that the upper density is at most1/2, including the branch \(p>R\), and hence lies in \([0,1)\) at every allowed prime.

For any real prime density \(g(p)\), the explicit function
\[
 \omega(d)=d\prod_{p\mid d}g(p)
\]
satisfies \(\omega(1)=1\), is multiplicative on coprime natural arguments, and obeys \(\omega(p)/p=g(p)\). It is defined at0 as well; the factor \(d\) makes that value zero. These statements require no unformalized number-theoretic input.

Scope: these files establish actual root counts, the candidate density bounds, and multiplicativity. The full paper local-density claims remain open until the candidates are connected to the actual normalized Euler products. The subsequent milestone supplies that connection and handles the possible zero upper base factor without dividing by it. The original manuscript is unchanged.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachSieveRootCounts.lean | 8 |
| GoldbachSieveDensityBounds.lean | 7 |
| GoldbachSieveDensityMultiplicative.lean | 4 |

- `goldbach_rho_eq`
- `goldbach_rho_congr`
- `goldbach_cohen_rho`
- `goldbach_rho_legendre`
- `goldbach_rho_le_two`
- `goldbach_rho_of_zero`
- `goldbach_rho_five_consecutive`
- `goldbach_prime_restricted_count`
- `goldbach_local_denominator_pos`
- `goldbach_local_density_nonneg`
- `goldbach_local_density_le`
- `goldbach_density_bound_lt_one`
- `goldbach_local_density_lt_one`
- `goldbach_upper_density_five`
- `goldbach_upper_density_range`
- `goldbach_sieve_omega_one`
- `goldbach_sieve_omega_prime`
- `goldbach_sieve_omega_mul`
- `goldbach_sieve_omega_div`

<!-- checkpoint-verification -->

## Verification

All 1288 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 5081-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 4124 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1290 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; all Section10 statements and the full circle-method implication are complete in the agreed conditional scope; Section11 remains open. The rational smooth multifrequency theorem with circle transference remains an explicit independent compound hypothesis. The classical primitive sum-of-two-squares criterion is an additional explicit independent arithmetic hypothesis for Section9 reductions; it contains no own-paper conclusion and is not declared as a Lean axiom.

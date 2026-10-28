# Checkpoint 1227: Complete lower-sieve application and mean-square error

The full lower-sieve application, stable source label `p:sieveneedlower8`, is proved in `goldbach_lower_sieve_complete`. This is a complete implication under independent classical inputs, not an unconditional formalization of those inputs. Both clauses of the source proposition are covered.

For every positive prescribed logarithmic saving A, the theorem constructs fixed B>=0, C>0 and M>0, a common real error eta(N) tending to zero, and for every sufficiently large integer N a coefficient family c_d chosen before n, with |c_d|<=1. For every n=12 mod24 it proves

\[
 X_n\Theta_n(z)\bigl(f_{1/2}(9/8)-\eta(N)\bigr)+\mathcal E_1(n)
 \leq S(\mathcal A_n,\mathbb P_{3,n},z),
 \qquad z=N^{8/9},
\]

and

\[
 \sum_{n<N^2}\mathcal E_1(n)^2\leq M N^4(\log N)^{-A}.
\]

The pointwise statement actually holds for every n in that residue class, so it includes the entire retained n range uniformly for every A0. The error is uniform because it is fixed before n; no density-dependent o(1) is introduced.

## Actual levels and the common error

The definitions use D=N/(24(log N)^B), D0=exp((log log N)^3), D1=D/D0 and R=(log N)^C. Lean proves log(D1)/log(N)->1, log(D1)/log(z)->9/8, D0*D1=D, and the eventual complete range R+1<=z<=D1<=N^2. Thus the classical one-stage theorem is used in its admissible range.

Write epsilon(N) for the already proved explicit uniform presieving error. The new error is exactly

\[
 \eta(N)=\varepsilon(N)+
 \left|f_{1/2}(\log D_1/\log z)-f_{1/2}(9/8)\right|.
\]

The first summand tends to zero by the quantitative presieve, and the second by the proved parameter limit and continuity of the classical sieve function at9/8. Positivity of the actual X_n and Theta_n permits the lower replacement. No numerical value or positivity of f_(1/2)(9/8) is assumed or needed here.

## Actual sequence and main term

The sequence consists of r-1 for the actual admissible representations n=m^2+r with m and r prime and r=11 mod24. The finite-index representation counts each admissible r once, and the image r->r-1 is proved injective on this set. Its divisibility counts are exactly the progression counts with one CRT residue a_d modulo24d. Those residues are fixed independently of n. Their coprimality and congruences are proved, not supplied as new hypotheses.

The density is the product over prime factors of the actual root-count density rho_p(n-1)/(p-1-rho_p(n)) for p<=R, and 1/(p-1) for p>R. Multiplicativity, normalization at1, the interval[0,1), and both refined dimension conditions are proved. The preliminary condition is obtained from the universal majorant2/(p-3) on p>=7, with dimension2. The outer condition has dimension1/2 on the fixed primes3 mod4.

X_n is the real part of the original arithmetic factor G_R(1,24,n)/phi(24) times the original smoothed singular integral. Lean proves the base factor real and strictly positive for n=12 mod24, and uses the already proved singular-integral nonnegativity. The divisor-count expansion uses this exact X_n and the original circle-method remainder. Theta_n is exactly the Euler product of the same local densities. The two split Euler products are proved to equal it.

The corrected presieving construction chooses coefficients before all density functions, finite sequences and n. Its actual fixed-prime sifted count is bounded above by the original n-dependent sifted count using the previously proved fixed-sieve comparison.

## Mean-square remainder

The remainder is the real signed sum over positive d<D of the original r_(24d,1)(n), with the fixed CRT residues. The embedding d->(1,24d) into the circle-method coefficient set is proved injective. Its moduli satisfy the strict bound24d<N(log N)^(-B). The coefficients have complex norm at most1. Thus the already proved circle-method theorem applies with the constant multiplier range L=2 and, for example, delta=1/2. Reindexing and |Re(z)|<=|z| give the stated real mean-square estimate. The zero denominator is assigned remainder0, so it introduces no artificial term.

## Independent hypotheses and limits

The exact unproved inputs consumed are ordinary prime Siegel-Walfisz, ordinary Bombieri-Vinogradov, the existing raw Ren/Ghosh estimates, the general one-stage Rosser-Iwaniec fundamental and coefficient estimates, the two general interval Mertens products, and continuity of the classical lower sieve function at9/8. The last property is part of the classical sieve-function boundary. All are theorem parameters or proposition-valued interfaces; none is a new Lean axiom. The Mertens interface mentions only arbitrary prime intervals and universal comparison factors. It contains no n, Goldbach sequence, source presieve, lower-sieve proposition or own-paper endpoint.

The selected manuscript is unchanged. The user is editing the compact presieving replacements; their application is not claimed without a new source or confirmation. No further manuscript replacement was found necessary for this lower-sieve milestone.

## Remaining work

Five substantive Goldbach claims remain: `l:maintermsize8`, `l:wumatomakisum`, `p:sieveneedupper8`, `l:numericalcomparison`, and `t:repmotthm`. The literal weaker presieving statement remains separately open pending manuscript synchronization, while its corrected conditional variant is already proved. The source ledger is now19 proved,28 complete conditional implications,1 quoted external theorem and6 open claims, plus4 definitions. Checkpoint numbers and supporting-theorem counts are not completion percentages.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachLowerSieveApplication.lean | 3 |

- `goldbach_lower_theta_positive`
- `goldbach_lower_presieve_application`
- `goldbach_lower_sieve_complete`

<!-- checkpoint-verification -->

## Verification

All 1309 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 5102-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 4228 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1311 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; all Section10 statements and the full circle-method implication are complete in the agreed conditional scope; Section11 remains open. The lower-sieve endpoint is proved from independent ordinary SW/BV, raw Ren/Ghosh, one-stage Rosser-Iwaniec, interval Mertens and classical sieve-function continuity inputs. No own-paper sieve or Goldbach endpoint is assumed. The full Section11 lower-sieve proposition p:sieveneedlower8 is a complete conditional implication, including its actual main term, uniform o(1), n-independent coefficients and mean-square error. The main-term size, weighted upper main-term sum, upper sieve, numerical comparison and final Goldbach conclusion remain open.

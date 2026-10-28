# Checkpoint 1224: Corrected full presieving from independent classical inputs

The corrected full presieving implication is proved in `goldbach_corrected_presieving`, conditional on the independent general one-stage Rosser–Iwaniec fundamental and coefficient inputs. Their exact interfaces are documented in `docs/EXTERNAL_SIEVE_INPUTS.md`. The literal original source lemma remains open until its weaker hypotheses are corrected. Proposed replacement passages are in `Section11_Presieving_Replacements.tex`. They have not been applied to the selected manuscript.

The primary source checked is Yuta Suzuki's [The Rosser–Iwaniec sieve](https://www.suzuyu1729.com/notes/NagoyaSeminar2022/RosserIwaniec.pdf), dated14 March2023. Definition8.2 requires the product bound with factor 1+K/log(w), rather than an unrestricted fixed factor K0. Lemma14.7 states the corresponding coefficient estimates with D>=z>=2. Proposition11.8 controls the sieve-function tails. The original official Iwaniec1980 PDF downloads returned403; this review does not claim they were read.

The corrected statement explicitly requires X>=0 and g(1)=1; X=0 is included. Three further points need to be explicit in the manuscript. First, the refined dimension estimate is stronger than a coarse implied-constant estimate. A fixed K0 allows a concentration of local mass at a few large primes, while 1+K/log(w) approaches1 at large w. Consequently the coarse estimate alone is not the hypothesis of the cited coefficient theorem. The refined interval forms of Mertens' theorem are available for the actual outer densities in this application; they must be stated and used.

Second, the preliminary prime set includes p=R. A dimension condition restricted to p<y with y<=R omits that endpoint if R is prime. The proposed formulation bounds the truncated preliminary prime set over all relevant intervals and uses sifting limit R+1. This retains exactly the intended primes p<=R.

Third, D0<D by itself does not place the outer sieve in the range D1>=z, and log(D0)/log(R) tending to infinity by itself does not give the rate needed to absorb arbitrary outer logarithmic losses. The proposed passage states the actual scale R=(log N)^C, the bound R+1<=z<=D1<=N^A, and the intended uniformity. These conditions give preliminary relative errors bounded by a constant times exp(-c(log log N)^2), which dominate every fixed negative power of log N. Applying these scale conditions to the final lower and upper sieve parameters is a separate later obligation.

The checked finite construction does not assume the paper's two-stage conclusion. It starts from independent one-stage lower and upper weight inequalities. For an outer lower coefficient u(d), the preliminary choice is the lower weight when u(d)>=0 and the upper weight when u(d)<0. For an outer upper coefficient, the choices are reversed. Lean proves the resulting pointwise inequalities, then sums them over actual finite sequences. The sequence is represented by a finite set of indices and an arbitrary integer-valued map, so repeated values are counted correctly.

Disjoint prime supports imply coprimality of every preliminary divisor e and outer divisor d. This gives unique decomposition of m=e*d. The flattened coefficient is explicitly the sum over pairs with that product. Lean proves its absolute value is at most1 and that it vanishes for m>=D0*D1. It also proves exact reindexing into the sum over all natural m<D0*D1, using the natural ceiling of the real level. None of these coefficient definitions mentions the density function, the sequence, X or the remainders.

For the main term, let V0 be the preliminary Euler product, and suppose each preliminary coefficient sum differs from V0 by at most epsilon0*V0. The error from either signed selection is proved to be at most

\[
\varepsilon_0 V_0\sum_d |u(d)|g(d).
\]

Together with the outer coefficient estimates, this proves explicit finite lower and upper inequalities with the original signed remainders. No positivity assumption on an outer signed weight is introduced. The uniform Euler-product bound and exact rate absorption are now proved and joined to the two independent classical one-stage interfaces in the complete corrected asymptotic deduction. No own-paper endpoint is assumed.

The source-level ledger remains19 proved claims,27 complete conditional implications,1 quoted external result and7 open claims. The presieving supporting theorems do not increase that count by themselves.

The signed outer mass M is proved to satisfy M/V1<=V1^(-2). The refined dimension condition at w=2 and log(z)<=A*log(N) give V1^(-1)<=K2*(log N)^kappa, with K2=(1+K/log 2)*(A/log 2)^kappa. Multiplicativity is needed only on supported square-free integers; its prime-product expression is proved internally.

For t=log(log N), D0=exp(t^3), and preliminary sifting limit exp(C*t)+1, the exact preliminary parameter satisfies s0>=t^2/(C+1) for t>=1. Lean proves this bound, eventual level admissibility and s0 tending to infinity. The explicit common relative error

\[
 \varepsilon(N)=K_1(\log D_1)^{-\delta}
 +K_0e^{-cs_0}\bigl(K_2(\log N)^\kappa\bigr)^2\longrightarrow0
\]

is proved uniformly before all admissible densities. For every sufficiently large N, the final coefficients are chosen before g, the finite sequence, X and the remainders. In the paper application they are therefore chosen before n. The main terms contain only the outer functions f_kappa and F_kappa. The natural-absolute-value bridge covers repeated and negative integer sequence values.

The original manuscript is unchanged. The corrected complete conditional variant is recorded separately from the literal-source inventory. Its independent one-stage inputs and classical function normalization remain unproved; the kernel audit verifies the consuming implication. The next mathematical milestone is the actual lower-sieve application.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachPresieveUniformAssembly.lean | 1 |
| GoldbachPresieveClassicalInputs.lean | 8 |

- `goldbach_presieve_uniform_assembly`
- `goldbach_density_restrict`
- `goldbach_refined_dimension_restrict`
- `goldbach_refined_dimension_total`
- `goldbach_presieving_from_classical_coefficients`
- `goldbach_presieve_source_R`
- `goldbach_corrected_presieving`
- `goldbach_integer_sequence_divisor_count`
- `goldbach_integer_sequence_sifted_count`

<!-- checkpoint-verification -->

## Verification

All 1304 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 5097-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 4204 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1306 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; all Section10 statements and the full circle-method implication are complete in the agreed conditional scope; Section11 remains open. The rational smooth multifrequency theorem with circle transference remains an explicit independent compound hypothesis. The classical primitive sum-of-two-squares criterion is an additional explicit independent arithmetic hypothesis for Section9 reductions; it contains no own-paper conclusion and is not declared as a Lean axiom.

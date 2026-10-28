# Checkpoint 1124: Complete the source logarithmic progression-energy estimate

The full source progression-energy bound e:remainingL2 is now proved from the printed numerical ranges. The exact terminal theorem goldbach_source_progression_energy_printed_range covers every natural N>=1 with log N>=1, every delta>0, every B>=0, every real L0<N^(2-delta), all varying real V_ell below sqrt(N^2/ell)(log N)^(-B), arbitrary real prime endpoint W, arbitrary residues and arbitrary complex coefficients of norm at most one.

Every elementary range condition of the efficient energy proof is discharged. The strict coefficient-index set gives positive ell and k; the L0 range implies ell<=N^2. For each nonempty row, V_ell>1. Monotonicity and the source cutoff give moduli at most N and card(K_ell)^2<=N^2/ell. Negative or too-small V_ell create empty rows and are not improperly squared. The logarithmic factor (log N)^(-B)<=1 and the real/Natural cutoff comparisons are proved explicitly.

The resulting literal circle integral is at most (256/log 2) N^2(log N)^6, with a constant independent of L0, V, residues, coefficients and W. The underlying general estimate at1123 is stronger, of order N^2(1+log N)^5. The proof groups arithmetic moduli before counting prime-product frequency multiplicities. It uses elementary prime-divisor logarithmic bounds and the checked congruence-square bound, and requires no PNT, Bombieri–Vinogradov, Siegel–Walfisz or new independent hypothesis.

The four new supporting theorems complete an unnumbered estimate inside the source hybrid-minor proof. The full l:hybridminorarc remains open until the actual prime-square logarithmic bound is supplied uniformly in its U range and combined with Bessel. The major-arc replacement/completion, combined l:circmethod, Section11 sieve/main-term/integral estimates and headline theorem remain open. No manuscript replacement is required by this alternative stronger formal proof.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachSourceEnergy.lean | 4 |

- `goldbach_source_row_cutoffs`
- `goldbach_source_energy_numerical_ranges`
- `goldbach_source_progression_energy`
- `goldbach_source_progression_energy_printed_range`

<!-- checkpoint-verification -->

## Verification

All 1191 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4982-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 3667 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1193 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; the Section10/11 analytic and sieve estimates remain open internal obligations. The rational smooth multifrequency theorem with circle transference remains an explicit independent compound hypothesis. The classical primitive sum-of-two-squares criterion is an additional explicit independent arithmetic hypothesis for Section9 reductions; it contains no own-paper conclusion and is not declared as a Lean axiom.

# Checkpoint 1123: Global logarithmic prime-progression energy bound

The global row-square summation is now proved. For arbitrary positive ell in [1,X], arbitrary row modulus sets contained in [1,M], and the local numerical constraint card(K_ell)^2<=X/ell, the total squared congruence multiplicity over 1<=t<=X/ell is at most X(H_M^3+1)H_X. The proof uses the exact interval square bound, natural-to-real division inequality and a nonnegative harmonic sum. It does not use a dyadic mean-square assertion.

For the actual weighted prime-progression polynomial, this gives the explicit integral bound (log(N^2)/log 2) N^2(H_N^3+1)H_(N^2), provided the arithmetic indices have positive ell<=N^2, row moduli at most N and the local row-cardinality constraint. These are elementary numerical conditions to be derived from the printed source cutoff, not new deep or analytic hypotheses.

The same theorem is converted to the explicit stronger bound (8/log 2) N^2(1+log N)^5 for every natural N>=1. Prime-frequency multiplicity was proved at1121, actual row grouping at1122 and every finite-sum step is checked. The four new supporting theorems use no PNT, progression-distribution or sieve input.

Before claiming the source estimate e:remainingL2, the printed varying V_ell cutoff and L0 range must still be shown to imply these numerical conditions. The next checkpoint supplies that source bridge and the required sixth-power logarithmic form. The full hybrid minor lemma, both major estimates and the headline remain open. No manuscript replacement is required; a formal proof may use a stronger route than the printed bookkeeping.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachLogarithmicEnergy.lean | 4 |

- `goldbach_harmonic_nonneg`
- `goldbach_total_row_square_bound`
- `goldbach_progression_energy_harmonic`
- `goldbach_progression_energy_log_five`

<!-- checkpoint-verification -->

## Verification

All 1190 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4981-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 3663 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1192 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; the Section10/11 analytic and sieve estimates remain open internal obligations. The rational smooth multifrequency theorem with circle transference remains an explicit independent compound hypothesis. The classical primitive sum-of-two-squares criterion is an additional explicit independent arithmetic hypothesis for Section9 reductions; it contains no own-paper conclusion and is not declared as a Lean axiom.

# Checkpoint 1173: Exact Upsilon unit expectation and frequency reduction

The actual unit sum is converted exactly to its finite canonical residue range. The lcm-compatible residue sum is identified with a unit sum on ZMod(lcm(k,q)), preserving the source residue restriction and all totient factors. Thus actual Upsilon is expressed as a normalized unit expectation with the source progression fixed.

The normalized pullback theorem proves the exact frequency reduction Upsilon(q*d,k,b,d*beta)=Upsilon(q,k,b,beta), for every positive denominator, multiplier and progression modulus and every coprime source residue. The proof checks both reduction maps and the exact additive-character scaling; no distribution or cancellation estimate is assumed. This is the precise nonprimitive-frequency bridge needed for the missing Upsilon decay.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachUpsilonReduction.lean | 5 |

- `goldbach_sum_units_range`
- `goldbach_unit_lcm_residue_sum`
- `goldbach_upsilon_lcm_unit_average`
- `goldbach_unit_reduction_comp`
- `goldbach_upsilon_frequency_reduction`

<!-- checkpoint-verification -->

## Verification

All 1240 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 5033-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 3904 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1242 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; the Section10/11 analytic and sieve estimates remain open internal obligations. The rational smooth multifrequency theorem with circle transference remains an explicit independent compound hypothesis. The classical primitive sum-of-two-squares criterion is an additional explicit independent arithmetic hypothesis for Section9 reductions; it contains no own-paper conclusion and is not declared as a Lean axiom.

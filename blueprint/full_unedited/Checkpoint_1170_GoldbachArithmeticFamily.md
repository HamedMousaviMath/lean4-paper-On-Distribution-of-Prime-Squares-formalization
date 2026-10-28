# Checkpoint 1170: Actual weighted arithmetic-family and finite-tail estimates

The full actual source family sum of norm G_q divided by ell phi(k) is bounded by9 exp(2) tau(q)^11(log N)²/q, uniformly in the residue family and n. The proof combines the actual general-modulus coefficient decay with the complete source harmonic estimate. The positive modulus and progression indices are justified from the exact strict finite family.

For any finite set S of positive denominators, bounded complex coefficients d, and kernel values H of norm at most a nonnegative M, the actual weighted arithmetic error is bounded by9 exp(2) M(log N)² times sum_{q in S}tau(q)^11/q. All finite sum exchanges and complex normalizations are proved. This applies to the explicit finite support obtained from the Euler series, but does not claim the missing quantitative smooth-denominator tail decay.

The separate progress map lists exactly what is complete and what remains: Upsilon decay, the actual cutoff replacement, addition of separated smooth denominators, the Rankin tail beyond Y, and final circle-method assembly. The full l:arithmeticcoefficients9, l:majorcompletion9 and l:circmethod remain open. The paper ledger is unchanged. No new external input or Lean axiom is introduced, and the selected manuscript is unchanged pending the user's updated source.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachArithmeticFamily.lean | 2 |

- `goldbach_source_arithmetic_coefficient_sum`
- `goldbach_source_finite_arithmetic_tail`

<!-- checkpoint-verification -->

## Verification

All 1237 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 5030-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 3894 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1239 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; the Section10/11 analytic and sieve estimates remain open internal obligations. The rational smooth multifrequency theorem with circle transference remains an explicit independent compound hypothesis. The classical primitive sum-of-two-squares criterion is an additional explicit independent arithmetic hypothesis for Section9 reductions; it contains no own-paper conclusion and is not declared as a Lean axiom.

# Checkpoint 1118: Explicit reciprocal-lcm logarithmic bound for the Goldbach energy

The reciprocal-lcm estimate used in the source diagonal and congruence-fibre square bounds is now proved with an explicit constant. For every natural V, the sum over 1<=a,b<=V of 1/lcm(a,b) is at most H_V^3, hence at most (1+log V)^3. The V=0 and V=1 endpoints are included. The strict real-cutoff version is also proved for every real V>=1 and all positive integers a,b<V; this matches the varying source modulus cutoffs without rounding them upward inside the logarithm.

The proof is elementary and uses no new deep input. Each denominator pair injects into the triple (gcd(a,b),a/gcd(a,b),b/gcd(a,b)). The lcm is proved equal to the product of these three quantities. For positive bounded denominators, all three entries lie in [1,V]. Nonnegative summation and the proved injection therefore bound the reciprocal-lcm sum by the full product of three harmonic sums. Mathlib's existing elementary harmonic/logarithm comparison supplies the explicit logarithmic bound.

The new five supporting theorems do not assume the reciprocal-lcm estimate, a sieve theorem, a mean-square result or the paper's hybrid lemma. They are direct Lean proofs. The next source step is the uniform count of simultaneous congruences in an interval, followed by the dyadic Cauchy–Schwarz collision bound O(N^2(log N)^6). The source prime-square minor bound must then be derived in its exact parameter range from independently recorded raw exponential-sum inputs. The full hybrid estimate and both major estimates remain open, so no source-level completion credit is awarded to l:hybridminorarc or l:circmethod. Section11 and the headline Goldbach theorem remain open.

Checkpoints1115,1116,1117 and1118 are saved separately. They respectively establish exact unweighted Fourier inversion, the actual weighted Bessel/partition/error assembly, exact collision energy and prime geometry, and the reciprocal-lcm logarithmic estimate. No new manuscript replacement is required by these four checkpoints. The user's reported manuscript edits are recorded without claiming a new upload or a remote edit.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachReciprocalLCM.lean | 5 |

- `goldbach_lcm_gcd_quotients`
- `goldbach_gcd_quotient_triple_injective`
- `goldbach_reciprocal_lcm_harmonic_cube`
- `goldbach_reciprocal_lcm_log_cube`
- `goldbach_reciprocal_lcm_strict_real_cutoff`

<!-- checkpoint-verification -->

## Verification

All 1185 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4976-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 3638 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1187 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; the Section10/11 analytic and sieve estimates remain open internal obligations. The rational smooth multifrequency theorem with circle transference remains an explicit independent compound hypothesis. The classical primitive sum-of-two-squares criterion is an additional explicit independent arithmetic hypothesis for Section9 reductions; it contains no own-paper conclusion and is not declared as a Lean axiom.

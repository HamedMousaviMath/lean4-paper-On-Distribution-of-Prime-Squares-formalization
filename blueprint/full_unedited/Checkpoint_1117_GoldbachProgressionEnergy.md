# Checkpoint 1117: Exact progression collision energy and off-diagonal prime geometry

The actual weighted progression energy has been opened by finite character orthogonality. The general goldbach_frequency_energy_identity proves the exact equality between the circle integral of the squared polynomial norm and the real part of the weighted sum over equal frequencies. Repeated frequencies are retained, so this is not an injectivity or disjointness assumption. Arbitrary complex coefficients are allowed.

For coefficients of norm at most one, goldbach_frequency_energy_le_collisions bounds the exact energy by the cardinality of the finite equal-frequency collision set. The actual progression events retain (ell,k,t), primality, the real W endpoint, ell*t<N^2 and the residue condition. The flat event polynomial is proved equal to the original nested progression polynomial. Thus goldbach_progression_energy_le_collisions is about the source's actual polynomial, not a replacement surrogate.

The composed goldbach_actual_minor_collision_bound has the literal natural-number output range n<N^2. It removes the free energy parameter from the earlier Bessel reduction and leaves only an explicit finite collision count and a pointwise prime-square minor bound. All coefficient and residue quantifiers remain arbitrary. Bounding that finite count by O(N^2 (log N)^6), and supplying the source uniform prime-square logarithmic bound, are still internal proof tasks; no such estimate is assumed to be a general external theorem.

The diagonal collision forces ell_1=ell_2. If t_1 and t_2 are distinct primes, the exact off-diagonal geometry ell_1=s*t_2 and ell_2=s*t_1 is proved, with a unique positive integer s whenever ell_1 is positive. This is the arithmetic starting point for the source dyadic Cauchy–Schwarz estimate.

All eight new supporting theorems are proved without a new independent deep input. Together, checkpoints1115–1117 prove the exact weighted Fourier bridge, measurable major/minor partition, actual Bessel inequality, explicit collision-energy reduction, diagonal/off-diagonal geometry and three-error assembly. The source hybrid logarithmic estimate, major approximation/completion, Bombieri–Vinogradov lemma, Section11 sieve/main-term/integral estimates and headline Goldbach theorem remain open. No manuscript replacement is newly required by this checkpoint.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachProgressionEnergy.lean | 8 |

- `goldbach_frequency_energy_identity`
- `goldbach_frequency_energy_le_collisions`
- `mem_goldbachProgressionEvents`
- `goldbach_weighted_progression_as_frequency_polynomial`
- `goldbach_progression_energy_le_collisions`
- `goldbach_actual_minor_collision_bound`
- `goldbach_prime_collision_diagonal`
- `goldbach_prime_collision_off_diagonal`

<!-- checkpoint-verification -->

## Verification

All 1184 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4975-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 3633 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1186 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; the Section10/11 analytic and sieve estimates remain open internal obligations. The rational smooth multifrequency theorem with circle transference remains an explicit independent compound hypothesis. The classical primitive sum-of-two-squares criterion is an additional explicit independent arithmetic hypothesis for Section9 reductions; it contains no own-paper conclusion and is not declared as a Lean axiom.

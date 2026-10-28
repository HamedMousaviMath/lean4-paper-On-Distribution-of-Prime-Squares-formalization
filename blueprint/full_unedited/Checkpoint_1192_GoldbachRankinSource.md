# Checkpoint 1192: Actual source smooth-modulus tail with arbitrary logarithmic saving

The exact source parameters R=(log N)^C and Y=N/(100sqrt(R)) are now substituted into the complete Rankin estimate. For every fixed C≥1 and desired t>0, one natural threshold is chosen before every supporting integer D and every finite divisor subset S. If all prime factors of D are at most R and every q in S exceeds Y, then sum_(q in S) tau(q)^11/q≤(log N)^(-t).

The proof checks R≥2, the positive Rankin exponent, its upper bound1/2, the sigma log R budget, and the exact exp(log N)=N substitution. The threshold is uniform in D,S and all arithmetic coefficient data. This is the arbitrary logarithmic saving used in the source tail argument, proved without a new Mertens or distribution hypothesis.

The actual weighted arithmetic-family tail is next, followed by the remaining small-modulus and disjoint added-modulus major estimates and final assembly.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachRankinSource.lean | 1 |

- `goldbach_source_rankin_tail`

<!-- checkpoint-verification -->

## Verification

All 1259 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 5052-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 3993 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1261 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; the Section10/11 analytic and sieve estimates remain open internal obligations. The rational smooth multifrequency theorem with circle transference remains an explicit independent compound hypothesis. The classical primitive sum-of-two-squares criterion is an additional explicit independent arithmetic hypothesis for Section9 reductions; it contains no own-paper conclusion and is not declared as a Lean axiom.

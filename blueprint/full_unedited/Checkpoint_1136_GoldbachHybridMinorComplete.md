# Checkpoint 1136: Complete source hybrid minor-arc estimate from raw Ren-Ghosh inputs

The full source hybrid minor-arc lemma l:hybridminorarc is now a complete implication under the existing independent raw UniformRenGhoshInputs. For every A>0, take C₀=3A+4d+26. Every real C≥C₀ is allowed; one N₀≥4 then works uniformly in all printed coefficient, residue and cutoff data. The actual mean square over n<N² is at most K N⁴(log N)^(-A), with K=Z²(256/log 2) and Z=(2P+3)/log 2. The theorem covers every B≥0, δ>0, the strict printed L₀ and V_ell ranges, all coefficients of norm at most1, all residue families, every real 0≤U≤N and arbitrary real W. Thus it includes the source ranges 2≤U≤N and 2≤W≤N². The minor set is the exact measurable complement of the closed source arcs of uniform radius (log N)^C/N². All Abel, proper-prime-power, halving, scale-transfer, logarithmic-parameter, progression-energy and Bessel steps are proved. No own-paper endpoint is assumed. This closes only the hybrid minor lemma; the full circle-method approximation and Section11 endpoints remain open.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachHybridMinorComplete.lean | 2 |

- `goldbachHybridMinorConstant_pos`
- `goldbach_hybrid_minor_complete`

<!-- checkpoint-verification -->

## Verification

All 1203 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4994-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 3721 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1205 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; the Section10/11 analytic and sieve estimates remain open internal obligations. The rational smooth multifrequency theorem with circle transference remains an explicit independent compound hypothesis. The classical primitive sum-of-two-squares criterion is an additional explicit independent arithmetic hypothesis for Section9 reductions; it contains no own-paper conclusion and is not declared as a Lean axiom.

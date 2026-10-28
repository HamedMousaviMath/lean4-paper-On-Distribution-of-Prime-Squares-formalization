# Checkpoint 1153: Uniform absorption of all strict-endpoint and nonunit prime errors

The actual coefficient-family cardinality satisfies card(I)²≤3N^(4-delta) log N under the printed strict L0 and logarithmic V_ell ranges. An explicit logarithm-versus-power budget is proved eventually. Combining the square bounds proves2(log N)^C card(I)≤N²(log N)^(-t) for every fixed desired saving, with one threshold independent of all cutoffs and residue data. Thus every retained1+q term from a strict prime endpoint or a prime dividing q is absorbed uniformly, since1+q≤2R. This closes the previously identified finite-boundary issue without changing the stated approximation theorem.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachMajorFiniteErrorAbsorption.lean | 4 |

- `goldbach_source_index_card_printed`
- `goldbach_major_finite_error_eventual`
- `goldbach_major_finite_error_numeric`
- `goldbach_source_finite_error_absorbed`

<!-- checkpoint-verification -->

## Verification

All 1220 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 5011-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 3802 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1222 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; the Section10/11 analytic and sieve estimates remain open internal obligations. The rational smooth multifrequency theorem with circle transference remains an explicit independent compound hypothesis. The classical primitive sum-of-two-squares criterion is an additional explicit independent arithmetic hypothesis for Section9 reductions; it contains no own-paper conclusion and is not declared as a Lean axiom.

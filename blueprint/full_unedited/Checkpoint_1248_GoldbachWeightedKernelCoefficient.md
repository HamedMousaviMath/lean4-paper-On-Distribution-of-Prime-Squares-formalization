# Checkpoint 1248: Weighted upper main term: effective source kernel and coefficient

# Weighted upper main term: effective arithmetic kernel

The actual finite kernel bound is now instantiated with the concrete strongly multiplicative mean and harmonic estimates. Its constants are chosen before the cutoff exponent, scale, and target integer. All remaining hypotheses are explicit scalar cutoff inequalities whose eventual validity has been proved.

The coefficient is normalized by (C_R/B_R)/(sqrt(log R) log(N) sqrt(log N)). Its exact factorization is checked, and its limit is (exp(-gamma/2)/sqrt(pi)+K epsilon^delta) W(9/8). The small-denominator and endpoint components tend to zero independently of n.

This is a complete effective kernel implication from the documented independent inputs. The original weighted main-term claim remains open pending the sharp eventual moving-kernel estimate and its singular-integral and relative-error assembly. No new external endpoint is assumed.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachWeightedKernelCoefficient.lean | 3 |
| GoldbachWeightedKernelEffective.lean | 1 |

- `goldbach_weighted_kernel_coefficient_limit`
- `goldbach_weighted_coefficient_factor`
- `goldbach_weighted_mean_interval`
- `goldbach_weighted_kernel_effective`

<!-- checkpoint-verification -->

## Verification

All 1350 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 5143-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 4409 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1352 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; all Section10 statements and the full circle-method implication are complete in the agreed conditional scope; Section11 remains open. Previously documented independent mean-value/Mertens inputs only. The full Section11 lower-sieve proposition p:sieveneedlower8 is a complete conditional implication, including its actual main term, uniform o(1), n-independent coefficients and mean-square error. The uniform main-term lower bound l:maintermsize8 and its joint application with the same large cutoff C are also complete conditionally. The weighted upper main-term sum, upper sieve, numerical comparison and final Goldbach conclusion remain open.

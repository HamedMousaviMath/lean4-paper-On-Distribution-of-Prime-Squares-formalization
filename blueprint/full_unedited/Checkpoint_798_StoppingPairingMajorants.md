# Checkpoint 798: Prove actual varying-scale high and low pairing bounds from Proposition 4.19

Proves finite variable-scale pairings from genuine real l2 pointwise majorants, then applies the exact countable high maximum and local low estimate of completed Proposition 4.19 at an arbitrary spatially varying dyadic arithmetic scale. The high pairing uses the actual supremum representative and its l2 norm. A fixed-scale norm is not substituted. These estimates are deductions from Proposition 4.19; no new external input is used. The local error maximum, ordinary-square stopping boundary and final sparse assembly are still separate work.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| StoppingPairingMajorants.lean | 4 |

- `finite_pairing_real_l2_majorant`
- `finite_threePiece_majorant_bound`
- `selectedPrimeHigh_stopping_pairing`
- `selectedPrimeLow_stopping_pairing`

<!-- checkpoint-verification -->

## Verification

All 865 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4472-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2250 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 867 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results under their paper hypotheses remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. Lemma 3.21, both conclusions of Theorem 1.1, all displayed clauses of Proposition 4.19 and both clauses of Proposition 6.21 are complete checked implications under their separately recorded independent deep inputs. The square-sign reflection is proved. The whole paper, the stronger printed auxiliary lemmas and the later sparse/ergodic/sieve applications remain unfinished. Proposition 4.19 consumes PrimeAsymptoticInputs, the refined PagePrimeSquareDistributionInputs c, RawPageUniquenessInput c and SmoothCircleBourgainInput C. These are independent raw analytic/data hypotheses, not own-paper operator conclusions or new Lean axioms. Theorem 1.1 retains its separately recorded older fixed-scale inputs and independent ordinary-square global decomposition; reflection is proved.

# Checkpoint 766: Derive dyadic exceptional-character uniqueness from the raw Landau-Page input

The independent Landau-Page input is now stated precisely for primitive nonprincipal quadratic characters and their real zeros. A zero below 1 is represented by the limit of ordinary Dirichlet-series partial sums, not by an unconditional tsum; the analytic-continuation bridge is explicitly part of the unformalized input. The standard uniqueness region itself remains an explicit general hypothesis, with no operator conclusion assumed. From it, Lean proves uniqueness of the complete character-and-zero datum in each dyadic conductor class after halving the region constant, and proves that source-region eligibility implies conductor-region eligibility. The standard input is documented against Philippe Michel's 2006 lectures, section 1.2 (Landau/Page), https://www.epfl.ch/labs/tan/wp-content/uploads/2018/10/Parkcitylectures.pdf. This does not change Theorem 1.1's previously recorded inputs.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| RawPageUniqueness.lean | 2 |

- `page_dyadic_uniqueness`
- `page_source_region_eligible`

<!-- checkpoint-verification -->

## Verification

All 833 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4440-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2079 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 835 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results under their paper hypotheses remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. In addition, Lemma 3.21 and BOTH conclusions of Theorem 1.1 are complete checked implications under their explicit independent deep inputs. The PNT limits are used in the sharp Gauss/high bound; an imported PNT bridge is not integrated. The whole paper, the full maximal clauses of Proposition 4.19/6.21 and the later headline applications remain unfinished. See docs/THEOREM_1_1_EXTERNAL_INPUTS.md. PNT limits, raw compatible progression/Ren/Ghosh data, and the independent square decomposition remain explicit hypotheses. The smooth multifrequency boundary is only for later maximal applications.

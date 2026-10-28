# Checkpoint 752: Localize actual annular sources with disjoint wider cutoffs

The actual circle source is localized by a wider cutoff: the wider cutoff equals one everywhere that the original cutoff is nonzero. The proof passes through the unique real lift, with the actual smooth bump's core radius 1/2 and support radius 1. A general denominator-separation statement proves disjointness of the wider cutoffs. For denominator blocks s >= 4, the cutoff at s-1 is both sufficiently wide to localize the source at s and sufficiently narrow to remain disjoint between distinct canonical centers. These facts will let the time-and-denominator maximum use orthogonal filtered inputs rather than pay for the number of denominators.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| NestedSourceLocalization.lean | 4 |

- `circleSourceCutoff_one_on_inner`
- `circleAnnularSource_localized`
- `circleSourceCutoff_general_disjoint`
- `predecessorSourceCutoff_geometry`

<!-- checkpoint-verification -->

## Verification

All 819 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4426-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2032 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 821 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results under their paper hypotheses remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. In addition, Lemma 3.21 and BOTH conclusions of Theorem 1.1 are complete checked implications under their explicit independent deep inputs. The PNT limits are used in the sharp Gauss/high bound; an imported PNT bridge is not integrated. The whole paper, the full maximal clauses of Proposition 4.19/6.21 and the later headline applications remain unfinished. See docs/THEOREM_1_1_EXTERNAL_INPUTS.md. PNT limits, raw compatible progression/Ren/Ghosh data, and the independent square decomposition remain explicit hypotheses. The smooth multifrequency boundary is only for later maximal applications.

# Checkpoint 767: Construct and verify the actual exceptional-character classes from Page uniqueness

The class parametrization is now proved from raw Page uniqueness. The construction chooses an occurring exceptional datum for each occupied dyadic conductor class and supplies a harmless principal-character fallback for empty classes. Lean proves that every active source datum equals its selected representative, that the representative conductor is at least 2^i, and that each selected character is quadratic. Source-region zero data imply the exact conductor-region eligibility used in the uniqueness proof. The selection includes the actual character and zero, not merely the conductor; no unverified identification is made when the exceptional character changes with scale.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| PageConductorClassSelection.lean | 7 |

- `optionPageBeta_nonneg`
- `optionPageBeta_le_one`
- `pageClassRepresentative_bin`
- `pageClassRepresentative_eq`
- `pageClassConductor_lower`
- `pageClassCharacter_quadratic`
- `pageSourceRegion_family_eligible`

<!-- checkpoint-verification -->

## Verification

All 834 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4441-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2086 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 836 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results under their paper hypotheses remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. In addition, Lemma 3.21 and BOTH conclusions of Theorem 1.1 are complete checked implications under their explicit independent deep inputs. The PNT limits are used in the sharp Gauss/high bound; an imported PNT bridge is not integrated. The whole paper, the full maximal clauses of Proposition 4.19/6.21 and the later headline applications remain unfinished. See docs/THEOREM_1_1_EXTERNAL_INPUTS.md. PNT limits, raw compatible progression/Ren/Ghosh data, and the independent square decomposition remain explicit hypotheses. The smooth multifrequency boundary is only for later maximal applications.

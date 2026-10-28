# Checkpoint 737: Sharp endpoint for the actual annular prime-square operator

Checks the exact leading coefficient c1*(2*sqrt(3)/9) and chooses every high coefficient c1>2 below a requested endpoint coefficient cstar>4*sqrt(3)/9. Instantiates the completed abstract Theorem 4.1 with the genuine annular von-Mangoldt kernel and independent ordinary-square input. This proves the sharp restricted endpoint for all sufficiently large dyadic arithmetic scales, with all constants quantified uniformly before the scale and finite sets. The result is conditional only on the explicit PNT, raw distribution and independent unweighted-square inputs. Full averages and the second main conclusion are not yet declared completed.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| PrimeSquareAnnularEndpoint.lean | 3 |

- `primeSquare_leading_coefficient`
- `exists_primeSquare_high_coefficient`
- `primeSquare_annular_endpoint_large`

<!-- checkpoint-verification -->

## Verification

All 804 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4411-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 1985 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 806 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. See docs/THEOREM_1_1_EXTERNAL_INPUTS.md. PNT limits, raw compatible progression/Ren/Ghosh data, and the independent square decomposition remain explicit hypotheses. The smooth multifrequency boundary is only for later maximal applications.

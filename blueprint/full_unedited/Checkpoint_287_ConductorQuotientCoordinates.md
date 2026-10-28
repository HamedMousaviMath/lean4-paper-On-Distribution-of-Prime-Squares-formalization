# Checkpoint 287: Exact real and natural conductor quotients and cutoffs

Exact real and natural conductor quotients and cutoffs. The conductor is positive, all quotient denominators are genuine natural quotients of multiples, and the exact real cutoff is retained. The set records both B0*d<=Q and q0*d<=floor(R), including their equality boundaries. B0 is the previously proved conductor majorant. No replacement of an arithmetic or source identity by a hypothesis is made.


## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| ConductorQuotientCoordinates.lean | 3 |

- `conductor_quotient_real`
- `conductor_quotient_positive`
- `conductor_quotient_cutoff`

<!-- checkpoint-verification -->

## Verification

All 354 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 3961-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 1399 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 356 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. Published Ren and Ghosh quadratic exponential-sum estimates, when consumed, remain displayed raw theorem hypotheses; the progression-prefix estimate also remains an explicit unproved input. No own-paper analytic conclusion is assumed.

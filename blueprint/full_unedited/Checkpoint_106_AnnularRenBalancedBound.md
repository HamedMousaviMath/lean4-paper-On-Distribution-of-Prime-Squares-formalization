# Checkpoint 106: The actual annular multiplier under the raw Ren estimate

This checkpoint applies the explicit Ren exponential-sum hypothesis to the actual annular von Mangoldt circle multiplier, using the newly proved weighted bracket estimate and the unconditional divisor budget. For N>=4, x=N/2, q<=sqrt(x), approximation precision |theta|<=1/(q*x^(3/2)), and effective denominator at least R/4, Lean proves

    norm(actual annular multiplier) <= (C*renDivisorConstant/2)*(log x)^c*renBalancedBudget(x,R).

The factor 1/2 comes from the exact N=2*x normalization. Positivity of the bracket, logarithmic base and selected divisor constant is proved. The q^(1/12) loss is consumed by the weighted estimates and has not been discarded. The raw Ren inequality still appears explicitly in the theorem hypothesis with its full tau(q)^(3/2) prefactor.

The theorem consumes a compatible raw estimate; it does not assert Ren's theorem for arbitrary unrelated xi and theta. Rational compatibility will be supplied by the selected approximation. No own-paper minor-arc conclusion or additional mathematical axiom is used.


## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| AnnularRenBalancedBound.lean | 2 |

- `renQuadraticBracket_nonneg`
- `annularMangoldt_Ren_balanced`

<!-- checkpoint-verification -->

## Verification

All 173 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 3695-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 1000 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 175 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. Published Ren and Ghosh quadratic exponential-sum estimates, when consumed, remain displayed raw theorem hypotheses; the progression-prefix estimate also remains an explicit unproved input. No own-paper analytic conclusion is assumed.

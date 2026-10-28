# Checkpoint 100: A fixed subpower budget for the exact Ren divisor prefactor

The unconditional divisor bound is raised to an arbitrary fixed positive real power gamma, retaining a constant uniform in the positive integer q. For each epsilon>0, Lean proves tau(q)^gamma<=C*q^epsilon by applying the previous bound at epsilon/gamma and justifying all real-power identities.

For the exact Ren prefactor gamma=3/2, a positive constant renDivisorConstant is selected from the proved existence theorem at the fixed exponent 1/12. Its positivity and the bound tau(q)^(3/2)<=renDivisorConstant*q^(1/12) are proved for every positive q. Neither exponent varies with q or N. No external analytic hypothesis is involved.

The aim is to insert this controlled prefactor into the subsequent Ren branch. This checkpoint does not claim that the q^(1/12) loss can be ignored or absorbed without further estimates. Full minor-arc and global approximation deductions remain open at this stage.


## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| RenDivisorBudget.lean | 3 |

- `divisors_card_rpow_le_rpow`
- `renDivisorConstant_pos`
- `ren_divisor_prefactor_bound`

<!-- checkpoint-verification -->

## Verification

All 167 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 3686-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 982 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 169 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. Published Ren and Ghosh quadratic exponential-sum estimates, when consumed, remain displayed raw theorem hypotheses; the progression-prefix estimate also remains an explicit unproved input. No own-paper analytic conclusion is assumed.

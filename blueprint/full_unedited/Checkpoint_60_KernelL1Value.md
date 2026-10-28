# Checkpoint 60: The bounded convolution sequence and its additive structure

The absolutely convergent convolution of a bounded kernel and an arbitrary l1 input is packaged as a genuine linfinity sequence. Its norm is proved at most B times the input norm, and addition of inputs is proved compatible with the sequence-valued construction using justified summation of the two absolutely convergent series. These results prepare the actual bounded linear low operator required by the abstract high-low framework.


## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| KernelL1Value.lean | 2 |

- `kernelL1Value_norm`
- `kernelL1Value_add`

<!-- checkpoint-verification -->

## Verification

All 127 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 3646-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 884 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 129 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. The already displayed raw progression-prefix estimate is consumed as a theorem hypothesis; it remains unproved. No new external analytic estimate or own-paper lemma is assumed.

# Checkpoint 92: The exact finite set of reduced canonical rational centers

A concrete finite set of canonical rational centers is defined, and its membership is proved exactly equivalent to 0<=r<1 and den(r)<=M. The construction enumerates a finite numerator-denominator box and filters by this exact predicate; it is not a sample or an incomplete denominator list. The normalized denominator is used, so fractions with different unreduced presentations do not introduce duplicate centers.

The proofs include the exact numerator and denominator ranges, monotonicity in M, the empty M=0 case, inclusion of the denominator-one center zero exactly when M>=1, and a finite cardinality bound. For a real cutoff R>=0, membership is proved equivalent to canonicality and den(r)<=R by using floor(R). This supplies the precise finite rational index set required by the model rather than leaving an arbitrary finite set as the only interface.

This identifies the reduced canonical rational index predicate. The character/coefficient data and complete summation correspondence are not silently supplied by this construction. No prime-distribution estimate, analytical approximation or deep input is used in these finite arithmetic proofs.


## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| CanonicalRationalCenters.lean | 7 |

- `mem_canonicalRationalCenters`
- `canonicalRationalCenters_parameters`
- `canonicalRationalCenters_mono`
- `canonicalRationalCenters_zero`
- `zero_mem_canonicalRationalCenters`
- `canonicalRationalCenters_card`
- `mem_sourceRationalCenters`

<!-- checkpoint-verification -->

## Verification

All 159 project modules and the root were freshly rebuilt: 3678 jobs pass without warnings/errors. All 947 named theorems pass the complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound. The source scan checks 161 Lean files. Exact unique import/audit coverage and unchanged frozen source hashes are checked before packaging. There are no placeholders or added mathematical axioms.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. The already displayed raw progression-prefix estimate is consumed as a theorem hypothesis; it remains unproved. No new external analytic estimate or own-paper lemma is assumed.

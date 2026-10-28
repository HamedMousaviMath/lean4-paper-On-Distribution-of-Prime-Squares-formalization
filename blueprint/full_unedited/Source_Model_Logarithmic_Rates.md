# Logarithmic rates for the actual source scale

For c,alpha>0 and A>=0, the module first proves the eventual estimate
\[
e^{-cx^\alpha}\le2^A(1+x)^{-A}.
\]
It composes the established exponential-versus-power limit with x^alpha, proves the exact power substitution on positive x, and handles the change from x to 1+x. The threshold depends on the fixed parameters.

For the already defined
\[
R(N,Q)=\max\{\exp((\log N)^{1/10}),Q^8\},
\]
the exact exponent split gives
\[
R^{-1/6}=R^{-1/16}R^{-5/48}
\le Q^{-1/2}e^{-(5/48)(\log N)^{1/10}}.
\]
Consequently, for each fixed A>=0, one natural N0 works for every Q>=1:
\[
N\ge N_0\Longrightarrow
R(N,Q)^{-1/6}\le2^A Q^{-1/2}(1+\log N)^{-A}.
\]
No upper bound on Q is needed for this parameter implication; the separate analytic estimates retain their own ranges.

A final general estimate proves that any fixed affine logarithmic factor A+B log R is eventually at most R^epsilon for epsilon>0. In particular,
\[
(A+B\log R)R^{-5/12}\le R^{-1/3}
\]
eventually. This matches the loss produced by counting finitely many active dyadic model terms.

| Module | New named theorems |
| --- | ---: |
| SourceModelLogarithmicRate.lean | 5 |

## Scope

All assertions are proved in Lean from the pinned Mathlib limits; no new analytic input is assumed. These estimates convert an established error rate. They do not themselves establish that rate for the actual prime-square symbol, or complete approximation 6.9 and its remaining minor-arc/periodization obligations.

<!-- checkpoint-verification -->

## Verification

All 105 project modules and the root were freshly rebuilt: 3624 jobs pass without warnings/errors. All 828 named theorems pass the complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound. The source scan checks 107 Lean files. Exact unique import/audit coverage and unchanged frozen source hashes are checked before packaging. There are no placeholders or added mathematical axioms.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. No new deep analytic input or own-paper lemma is assumed.

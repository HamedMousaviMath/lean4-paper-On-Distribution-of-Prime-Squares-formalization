# Frequency decay for the genuine annular models

The exact integration-by-parts identity and the two bounds \(4/N\) give, for \(N\ge2,\ 0\le\beta\le1\),
\[
4\pi|\theta|\,|M_N^\beta(\theta)|\le8/N^2.
\]
Thus, at nonzero frequency,
\[
|M_N^\beta(\theta)|\le\frac2{\pi|\theta|N^2}.
\]
Both statements are proved for the actual real integral. Its interval avoids the stationary point zero; no external oscillatory-integral theorem is assumed.

Combining the decay with the already proved half bound yields a global profile, valid also at zero:
\[
|M_N^\beta(\theta)|\le
\frac{1/2+2/\pi}{1+N^2|\theta|}.
\]
Finally, for positive real q and R, outside the rational arc
\[
|\theta|\ge R/(qN^2)
\quad\Longrightarrow\quad
|M_N^\beta(\theta)|\le2q/(\pi R).
\]
This last estimate is intended for the model-tail argument with q<=R. It retains prime-square spatial scale N^2.

| Module | New named theorems |
| --- | ---: |
| AnnularModelDecay.lean | 5 |

## Scope

No deep analytic input is used. These uniform-beta estimates supply the decay needed for model tails. They do not claim the extra N^(beta-1) factor in the manuscript's displayed estimate. The independent minor-arc gap is unchanged, and the full approximation and decomposition remain open.

<!-- checkpoint-verification -->

## Verification

All 100 project modules and the root were freshly rebuilt: 3615 jobs pass without warnings/errors. All 794 named theorems pass the complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound. The source scan checks 102 Lean files. Exact unique import/audit coverage and unchanged frozen source hashes are checked before packaging. There are no placeholders or added mathematical axioms.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. No new deep analytic input or own-paper lemma is assumed.

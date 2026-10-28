# Checkpoint 1252: Weighted upper main-term comparison complete

# Weighted upper main term: complete conditional formalization

The source lemma **l:wumatomakisum** is complete in uniform epsilon form. Its checked endpoint is `goldbach_weighted_upper_main_term_complete` in `PrimeSquares/GoldbachWeightedUpperMainTerm.lean`.

For every A>0, every fixed C>=A+24, and every eta>0, one threshold in N works for every n=12 modulo24 with N^2(log N)^(-A)<=n<N^2. With R=(log N)^C and alpha=9/8, the actual source sum satisfies

\[
\sum_{\ell\in L} X_n(\ell)\Theta_{n,\ell}(z_\ell)
\le (c_\alpha\mathcal W(\alpha)+\eta)X_n\Theta_n(z),
\qquad c_\alpha=\frac{16e^{-\gamma/2}}{\sqrt{\pi\alpha}}.
\]

This is the source uniform o(1) statement. The original main terms, multiplier set, local factors, Euler products and singular integrals are used. No paper conclusion is an external hypothesis.

The proved chain includes the arithmetic cancellation, strong multiplicativity and uniform prime-balance application, the small-denominator estimate, both finite Abel arguments, the prime endpoint p=z, the exact W integral, the sharp fixed and moving kernel, finite integration, total smoothing error, the discarded region, and the final positive lower comparison. A=the retained-range exponent, A+14 is a sufficient integration cutoff exponent, and C>=A+24 suffices for all error estimates.

The explicit independent hypotheses are the generic effective half-dimensional mean-value corollary of the corrected Tenenbaum theorem, ordinary/fixed-progression logarithmic Mertens estimates, the three ordinary relative Euler-product estimates, and the previously recorded interval-product Mertens bound. Their precise general interfaces and unformalized classical corollary reductions are in `docs/EXTERNAL_WEIGHTED_MEAN_INPUTS.md`. They are theorem parameters, not new Lean axioms. The entire weighted source application is proved. This milestone does not require a new Goldbach, weighted-prime-counting, or Siegel-Walfisz endpoint as an assumption.

The accompanying full build, source audit and exact axiom audit must pass before this checkpoint can be saved by the checkpoint driver. The selected manuscript and all accepted source hashes remain unchanged. The claim ledger moves from29 to30 completed conditional implications, leaving4 open entries: the upper sieve, numerical comparison, final Goldbach theorem, and the original weaker presieving statement awaiting source synchronization. The latter is bookkeeping about the manuscript; its corrected stronger variant is already formalized.

## Files and continuation

The complete project is in the checkpoint ZIP, including the pinned Lean/Mathlib configuration, all earlier proofs, verification records and recovery instructions. `blueprint/Weighted_Upper_Main_Term_Complete.md` presents the complete mathematical proof by topic. The next substantive milestone is the full upper-sieve application `p:sieveneedupper8`.

## Suggested paper replacements

The lemma statement and constant need no change. The following two proof edits are saved in `docs/WEIGHTED_UPPER_MAIN_TERM_REPLACEMENTS.tex`; they have not been applied to the selected manuscript.

1. In Step1, replace the passage beginning “Finally, since \(p_2>z\) and \(\ell=2up_2\geq p_2\), we have” through “all sufficiently large \(N\)” with:

```latex
Finally, since \(p_2\geq z\) and \(\ell=2up_2\geq p_2\), we have
\[
 z_\ell
 =\left(\frac{N^2}{\ell}\right)^{1/4}
 \leq\left(\frac{N^2}{p_2}\right)^{1/4}
 \leq\left(\frac{N^2}{z}\right)^{1/4}
 =N^{5/18}<N^{8/9}=z.
\]
Thus \(p_2\geq z>z_\ell\), and, since \(R=(\log N)^C\), also
\(p_2>R\) for all sufficiently large \(N\).
```

This preserves the inclusive endpoint in the definition of L.

2. In Step6, replace “Applying \eqref{e:Wsum10} on the remaining range gives” through “Therefore”, immediately before the existing display labelled `e:integratedW10`, with:

```latex
On the retained range \(m(y)\geq N^2(\log N)^{-A_1}\), we have
\(\log m(y)=(2+o(1))\log N\). Applying \eqref{e:Wsum10} therefore gives
\[
 \sum_{\substack{\ell=2up_2\in L\\2\ell\leq m(y)}}
 \frac{h_R(u)}{\ell(\log(m(y)/\ell))^2}
 \leq
 \left(\frac{e^{-\gamma/2}}{\sqrt\pi}\mathcal W(\alpha)+o(1)\right)
 \frac{C_R(n)}{B_R(n)}
 \frac{1}{\sqrt{\log R}(\log N)^{3/2}}.
\]
For these \(y\), we also have \(2\leq n-y^2\leq N^2\), so
\((\log y)^{-1}\leq
2\log N/(\log y\log(n-y^2))\).
The indicator in the definition of \(H_1(n)\) equals one on this range.
Integrating the preceding bound, and including the already estimated
 discarded region, gives the following inequality. For the latter error,
use \(C_R(n)/B_R(n)\geq1\) and \eqref{e:H1elementary10}, choosing
\(A_1\) sufficiently large in terms of \(A_0\).
```

Keep the existing `e:integratedW10` display unchanged. Equality at finitely many boundary points does not change the integrals. This edit retains the cutoff where the real logarithmic powers are valid and compares directly with H_1(n), without a separate shift asymptotic.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachWeightedSourceBridge.lean | 1 |
| GoldbachWeightedUpperMainTerm.lean | 1 |

- `goldbach_weighted_source_bridge`
- `goldbach_weighted_upper_main_term_complete`

<!-- checkpoint-verification -->

## Verification

All 1358 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 5151-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 4429 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1360 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; all Section10 statements and the full circle-method implication are complete in the agreed conditional scope; Section11 is complete through the weighted main-term comparison; the upper sieve and final Goldbach deductions remain open. Independent general effective mean-value and classical Mertens hypotheses remain explicit and unproved; all own weighted upper main-term deductions are complete. Earlier independent theorem scopes are unchanged. The full Section11 lower-sieve proposition p:sieveneedlower8 is a complete conditional implication, including its actual main term, uniform o(1), n-independent coefficients and mean-square error. The uniform main-term lower bound l:maintermsize8 and its joint application with the same large cutoff C are also complete conditionally. The full weighted upper main-term comparison l:wumatomakisum is a complete checked implication from the documented independent effective mean-value and Mertens inputs, with the exact printed constant and uniform retained-range quantifiers. The upper sieve, numerical comparison and final Goldbach conclusion remain open.

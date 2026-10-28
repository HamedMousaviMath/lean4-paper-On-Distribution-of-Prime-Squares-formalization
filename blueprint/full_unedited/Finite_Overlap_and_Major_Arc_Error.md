# Finite overlap and the genuine major-arc model error

This checkpoint combines actual finite rational-center symbols, genuine Gauss sums, the normalized annular integrals, and the constructed smooth cutoff. It proves a major-arc error estimate while preserving the unresolved minor-arc and global-model obligations.

## Counting all active scales

For a canonical center \(r\in[0,1)\), a reduced denominator below four forces
\[
r\in\{0,\tfrac12,\tfrac13,\tfrac23\}.
\]
This is an exact rational proof, not a numerical probe. The first two dyadic scales therefore contribute at most four active centers. For larger scales, the previously proved support separation makes the map \(r\mapsto\lfloor\log_2\operatorname{den}(r)\rfloor\) injective on active centers.

If every denominator in a finite canonical center set Gamma is at most M, the total active count is at most \(\lfloor\log_2 M\rfloor+5\). With denominators at most a real \(R\ge1\), a proved floor/log comparison gives
\[
\#\{\text{active centers}\}\le5+\frac{\log R}{\log2}.
\]
The finite-norm theorem first removes all inactive terms exactly and only then applies this count.

## Geometry of the selected major arc

For \(N>0,R>0\), rational arcs of denominators at most R and radii \(R/(qN^2)\) are disjoint under the explicit sufficient condition
\[
2R^3<N^2.
\]
Hence every other center lies outside its own major arc. The actual dyadic cutoff at the chosen center equals one under
\[
2R^4\le N^2.
\]
The real rational center plus its real offset is proved to equal the target circle frequency after coercion, retaining the true negative-phase annular symbol.

## Bounding the actual error

Let \(C_G>0\) be one unconditional constant selected from the already proved uniform Gauss-model theorem. It is uniform in N, modulus, character, unit coefficient and allowed exceptional coefficient. Assume \(N\ge2,\ 0<\beta\le1,\ |\kappa_r|\le1\), one shared character/coefficient family, and Gamma contained in [0,1) with denominators at most R.

At a selected \(r_0\in\Gamma\), put \(q_*=\operatorname{den}(r_0)\), \(\theta=\xi-r_0\), and assume
\[
|\theta|\le R/(q_*N^2).
\]
The raw progression-prefix estimate is the same explicit hypothesis used in the earlier major-arc proof:
\[
\left|\Psi_{q_*,u}(t)-H_{q_*,\kappa_{r_0}\chi_{r_0}(u),\beta}(t)\right|
\le NC e^{-c\sqrt{\log N}},\qquad N/2\le t\le N.
\]
The theorem also retains the earlier explicit parameter budgets
\(\log R\le\log N\), \(R^5\log N\le\sqrt N\), and
\(7\log R\le c\sqrt{\log N}\), together with the geometry conditions above.

Removing the chosen center exactly, applying its cutoff core identity, and bounding all remaining model terms gives
\[
\left|\widehat{\widetilde A}_{N,\Lambda}(\xi)-V_\Gamma(\xi)\right|
\le
\frac{4+(2+4\pi)C}{R^5}
+\left(5+\frac{\log R}{\log2}\right)\frac{4C_G}{\pi}R^{-5/12}.
\]
This is a proved bound for the actual von Mangoldt symbol, including prime powers. Its analytic caller consumes the raw prefix estimate; the paper's own minor-arc lemma is not an assumption.

For every fixed C>=0, the complete displayed right-hand side is also proved eventually at most \(R^{-1/6}\). The prior checkpoint provides the source-scale conversion of that rate to \(Q^{-1/2}(1+\log N)^{-A}\).

| Module | New named theorems |
| --- | ---: |
| RationalArcOverlap.lean | 6 |
| MajorArcGeometry.lean | 4 |
| MajorArcModelError.lean | 7 |

## Scope and next obligations

The raw progression estimate remains an explicit deep input. No existence theorem for one uniform choice of exceptional data is registered. Gamma is an explicit finite center set; this checkpoint does not construct the global source center set or identify a periodized model on the circle. In particular, the real integral with noninteger integration variable is not silently treated as periodic.

The full-range minor-arc deduction, global approximation 6.9, low 6.14, multifrequency 6.16, high/maximal 6.21, Proposition 4.19 and Theorem 1.1 remain open. The frozen manuscript and accepted revisions are unchanged. These open proof obligations do not establish a counterexample or prescribe a manuscript correction.

<!-- checkpoint-verification -->

## Verification

All 108 project modules and the root were freshly rebuilt: 3627 jobs pass without warnings/errors. All 845 named theorems pass the complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound. The source scan checks 110 Lean files. Exact unique import/audit coverage and unchanged frozen source hashes are checked before packaging. There are no placeholders or added mathematical axioms.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. The already displayed raw progression-prefix estimate is consumed as a theorem hypothesis; it remains unproved. No new external analytic estimate or own-paper lemma is assumed.

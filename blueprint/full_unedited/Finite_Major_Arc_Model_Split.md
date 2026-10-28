# Finite major-arc symbols and the exact high-low split

For a finite rational center set Gamma, the module uses the actual reduced numerator and denominator of each center r. It defines
\[
P_r(\xi)=\mathfrak s(r_{\rm num},r_{\rm den})M_N^1(\xi-r),\qquad
X_r(\xi)=-\mathfrak s_{\chi_r}(r_{\rm num},r_{\rm den})\kappa_r M_N^\beta(\xi-r).
\]
One beta and one family of character/coefficient data are shared over Gamma. The broad model term is
\((P_r+X_r)\eta_{\log_2(r_{\rm den})}(\xi-r)\), and V is their finite sum. Its equality to the previously defined localized genuine Gauss model is proved.

The ordinary low term uses the cutoff
\(\eta((qN^2/Q)(\xi-r))\) when q<=Q. Its high complement uses broad-minus-narrow in that case and the full broad term otherwise. The exceptional terms use
\(\eta((B_0(q/q_0)N^2/Q)(\xi-r))\), with selection \(q/q_0\le Q/B_0\).
For the source application, the coefficient kappa vanishes when q0 does not divide q, and q/q0 is the source d. The algebra is valid for the broader parameter family without asserting the existence of source exceptional data.

Splitting the ordinary and exceptional cutoff cases gives, exactly,
\[
\operatorname{Low}+\operatorname{High}=V,\qquad
\widehat{\widetilde A}_{N,\Lambda}
=\operatorname{Low}+\operatorname{High}
+(\widehat{\widetilde A}_{N,\Lambda}-V).
\]
The error here is the difference from the actual annular von Mangoldt symbol, including prime powers.

| Module | New named theorems |
| --- | ---: |
| FiniteMajorArcModels.lean | 5 |

## Scope

These are real-frequency finite symbols and exact identities. The selected finite center set remains an argument. No global periodization or analytic norm estimate is claimed by defining the error as a difference. The full approximation, low/high operator estimates, minor-arc bridge and Theorem 1.1 remain open.

<!-- checkpoint-verification -->

## Verification

All 104 project modules and the root were freshly rebuilt: 3623 jobs pass without warnings/errors. All 823 named theorems pass the complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound. The source scan checks 106 Lean files. Exact unique import/audit coverage and unchanged frozen source hashes are checked before packaging. There are no placeholders or added mathematical axioms.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. No new deep analytic input or own-paper lemma is assumed.

# A uniform explicit major-arc error budget

Checkpoint 27. This unit reduces the proved error for the actual annular
von Mangoldt symbol to a single R-dependent bound. It uses the raw
progression-prefix hypothesis from checkpoint 26; no new distribution
theorem or own-paper conclusion is assumed.

For N>=1, q>=1, R>=1 and delta>=0, suppose

\[
 q\leq R^{11/10},\qquad
 |\theta|\leq\frac{R}{qN^2},\qquad
 |C_{q,u}(t)-H_{q,\kappa\chi(u),\beta}(t)|\leq N\delta
 \quad(N/2\leq t\leq N)
\]

for every reduced residue u. The actual C,H,chi and beta>0 are the
objects defined in the previous unit. The same exceptional data are used
throughout this interval; no consistency across different N is asserted.

## The denominator and frequency calculation

The width condition implies q*abs(theta)*N^2<=R, by multiplying by the
positive q*N^2. Since R>=1, real-power monotonicity gives
R^(11/10)<=R^2, and also R<=R^2. Totient(q)<=q therefore implies

\[
 \phi(q)\delta(2+4\pi|\theta|N^2)
 \leq\delta(2q+4\pi R)
 \leq (2+4\pi)R^2\delta.
\]

This explicitly removes the dependence on q and theta from the residue
error in the whole source major-arc range. Positivity conditions are
displayed in Lean rather than used implicitly in denominator cancellation.

Monotonicity of the logarithm and log(R^2)=2*log(R) give
log(q)<=2*log(R). Substitution into the previously proved nonunit bound
produces the following result for the genuine finite Fourier symbol:

\[
 \begin{aligned}
 \big|\widehat{\widetilde A}_{N,\Lambda}(a/q+\theta)
 &-\big(\mathfrak s(a,q)M_{N,1}(\theta)
       -\mathfrak s_\chi(a,q)\kappa M_{N,\beta}(\theta)\big)\big|\\
 &\leq\frac{2\log R+2\sqrt N\log N}{N}
       +(2+4\pi)R^2\delta.
 \end{aligned}
\]

`annularMangoldt_majorArc_source_R_budget` is the paper-facing theorem.
An earlier theorem proves the same bound under the weaker denominator
restriction q<=R^2. This is a quantitative implication, with an explicit
constant, all prime powers retained and the exact annular normalization.

## Scope and continuation

The next step absorbs these two positive errors into a constant times
R^-5 and proves the required parameter inequalities for the source's
R=max(exp((log N)^(1/10)),Q^8). The raw progression estimate remains
an explicit analytic input. The independent minor-arc statement and full
Lemma 6.5 remain open. Theorem 1.1 is an explicit later target, after
Proposition 4.19 and the application of the proved abstract high-low result.

| Module | New named theorems | Result |
|---|---:|---|
| MajorArcErrorBudget.lean | 6 | Positive-denominator phase budget, real-power and logarithmic bounds, totient error control and actual major-arc error reduction |

There is no new numerical experiment or new deep assumption in this unit.

<!-- checkpoint-verification -->

## Verification

All 91 project modules and the root were freshly rebuilt: 3606 jobs pass without warnings/errors. All 745 named theorems pass the complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound. The source scan checks 93 Lean files. Exact unique import/audit coverage and unchanged frozen source hashes are checked before packaging. There are no placeholders or added mathematical axioms.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. No new deep analytic input or own-paper lemma is assumed.

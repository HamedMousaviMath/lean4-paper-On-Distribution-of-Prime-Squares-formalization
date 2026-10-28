# An actual smooth cutoff and its rational-arc geometry

The module constructs a real smooth bump centered at zero, with inner radius 1/2 and outer radius 1. Mathlib supplies the constructed function; its properties are proved rather than postulated:
\[
\eta\in C^\infty,\quad \eta(-x)=\eta(x),\quad 0\le\eta\le1,\quad
\eta(x)=1\ (|x|\le1/2),\quad \eta(x)=0\ (|x|\ge1).
\]

For the actual dilate \(\eta_s(\theta)=\eta(16^s\theta)\), a nonzero value implies \(|\theta|<16^{-s}\). The identity \(16^s=(2^s)^4\) gives the major-arc core assertion:
\[
q\le R,\quad 2^s\le q,\quad 2R^4\le N^2,\quad
|\theta|\le R/(qN^2)\quad\Longrightarrow\quad\eta_s(\theta)=1.
\]
The proof keeps all constants and proves the required positivity before dividing.

For \(s\ge2\),
\[
2\,16^{-s}< (2^{s+1})^{-2}.
\]
The preceding rational-separation theorem therefore implies uniqueness of an active rational center whose reduced denominator is at most \(2^{s+1}\).

| Module | New named theorems |
| --- | ---: |
| SourceArcCutoff.lean | 13 |

## Scope and small scales

This proves uniqueness only for s>=2. The first two scales remain for a finite overlap estimate; the strict radius inequality is not silently asserted for them. These functions currently live on real frequencies. The real quadratic integral is not treated as periodic in a noninteger integration variable. The full minor-arc bridge, approximation and high-low operator conclusions remain open.

<!-- checkpoint-verification -->

## Verification

All 102 project modules and the root were freshly rebuilt: 3621 jobs pass without warnings/errors. All 813 named theorems pass the complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound. The source scan checks 104 Lean files. Exact unique import/audit coverage and unchanged frozen source hashes are checked before packaging. There are no placeholders or added mathematical axioms.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. No new deep analytic input or own-paper lemma is assumed.

# Checkpoint 97: A fixed-epsilon Ghosh bound in the balanced denominator range

This checkpoint introduces the explicit Ghosh quadratic bracket 1/q+x^(-1/2)+q/x^2 and proves that, throughout x^(1/2)<=q<=x^(3/2), it is at most 3*x^(-1/2). Raising to the fourth power root gives 3^(1/4)*x^(-1/8), with positivity proved rather than assumed.

The actual annular von Mangoldt circle multiplier is related exactly to the positive-phase Ren sum on (N/2,N], with its 1/N normalization. From the displayed raw Ghosh estimate with the fixed epsilon=1/16, Lean proves a bound (B*3^(1/4)/2)*(N/2)^(-1/16) for this actual multiplier in the balanced denominator range. The epsilon is fixed once; it is never chosen as a function of N. This gives a polynomial saving in that range.

The deep Ghosh estimate is not formalized or added as an axiom. It is an explicit inequality hypothesis of the consuming theorems. Its source is A. Ghosh, The Distribution of alpha p^2 Modulo 1, Proc. London Math. Soc. 42 (1981), Theorem 2, with coprimality and strict approximation error <1/q^2. The original article's first-page transcription was inspected at https://www.academia.edu/60387191/The_Distribution_of_p2_Modulo_1 and its publisher identity is https://doi.org/10.1112/plms/s3-42.2.252. The annular form is also explicitly displayed as equation (1.4) of Xiumin Ren's author preprint https://www.math.hku.hk/imrwww/IMRPreprintSeries/2004/IMR2004-9.pdf. The consumer assumes the displayed raw inequality itself; it does not assert it for arbitrary incompatible choices of q and xi. Exact rational selection and compatibility are subsequent tasks.

This supplies the complementary balanced-denominator branch, not yet a full minor-arc theorem. A new approximation at precision x^(-3/2) is planned so that its larger denominators lie in this range. The smaller-denominator branch will use Ren, with its divisor prefactor controlled explicitly. The source's stronger printed minor-arc estimate remains open; no LaTeX correction is established by this checkpoint.


## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GhoshBalancedBound.lean | 5 |

- `ghoshQuadraticBracket_nonneg`
- `ghoshQuadraticBracket_balanced`
- `ghoshBalanced_fourth_root`
- `annularMangoldt_from_Ghosh_bound`
- `annularMangoldt_Ghosh_balanced`

<!-- checkpoint-verification -->

## Verification

All 164 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 3683-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 973 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 166 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. Published Ren and Ghosh quadratic exponential-sum estimates, when consumed, remain displayed raw theorem hypotheses; the progression-prefix estimate also remains an explicit unproved input. No own-paper analytic conclusion is assumed.

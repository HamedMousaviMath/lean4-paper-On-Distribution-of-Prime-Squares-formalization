# Checkpoint 862: Actual annular IW symbols and primitive-character identification

The actual annular low symbol is now connected to the real-line/IW operator interface, with a proved bounded continuous real symbol and exact equality to the finite periodized circle symbol. Lean also identifies a primitive character induced to the IW period with its original masked quadratic coefficients at every IW rational frequency. The principal and induced-character whole-sum identities are proved, including the conductor-not-dividing zero case. This supplies a concrete low operator for the comparison; no general-p continuous or low maximal bound is claimed by this identification.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| IWActualAnnularSymbols.lean | 7 |

- `annularCutoffSymbol_norm_half`
- `annularBoundedSymbol_apply`
- `annularBoundedSymbol_support`
- `iwCyclicSymbol_annular`
- `cyclicRationalCoefficient_primitive_induced`
- `iw_principal_width_symbol`
- `iw_induced_width_symbol`

<!-- checkpoint-verification -->

## Verification

All 929 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 4548-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 2559 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 931 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed source results under their paper hypotheses remain unchanged. Lemma 3.21, both conclusions of Theorems 1.1 and 1.3, all displayed clauses of Proposition 4.19 and both clauses of Proposition 6.21 are complete checked implications under their separately recorded independent deep inputs. The square-sign reflection is proved. Theorem 1.3 has actual finite sparse families, disjoint major subsets and the literal full all-cutoff maximum. The three general Section5 auxiliary statements remain partial, and the later Orlicz/ergodic/sieve applications remain unfinished. Proposition 4.19 consumes PrimeAsymptoticInputs, the refined PagePrimeSquareDistributionInputs c, RawPageUniquenessInput c and SmoothCircleBourgainInput C. These are independent raw analytic/data hypotheses, not own-paper operator conclusions or new Lean axioms. Theorem 1.1 retains its separately recorded older fixed-scale inputs and independent ordinary-square global decomposition; reflection is proved. Sparse applications additionally record OrdinarySquareStoppingInput CS and IndependentPrimeMaximalInput as explicit independent analytic boundaries. Their existence and the exact normalization/support/sign adaptations remain unproved; neither predicate contains this paper's endpoint or sparse conclusion. Section7 additionally records the independent RawTaoArcConstructionInput C, used only to obtain actual finite IW frequency geometry. Its existence is unproved; multiplier, sampling, low and high norm estimates are not fields and remain unfinished.

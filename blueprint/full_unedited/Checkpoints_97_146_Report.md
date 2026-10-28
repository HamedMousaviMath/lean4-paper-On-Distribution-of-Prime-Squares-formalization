# Prime Squares: checkpoints 97–146

This batch contains **50 separately verified checkpoints**, adding **136 named supporting theorems in 50 modules**. The final project has **213 modules and 1104 named supporting theorems**. These are counts of supporting declarations, not counts of completed manuscript theorems.

The main mathematical advance is a conditional global circle-model approximation and a conditional quantitative countable dyadic maximal-error bound. A new complementary minor-arc argument resolves the range left uncovered by direct substitution into Ren's estimate. Theorem 1.1 and the separate sharp low/high inputs remain open.

## Mathematical results

Write $x=N/2$ and $R=\max(\exp((\log N)^{1/10}),Q^8)$. The argument uses the actual annular von Mangoldt square multiplier, its actual continuous periodized circle model, and the corresponding genuine bounded operators on $\ell^2(\mathbb Z)$.

1. **An unconditional divisor budget.** For every fixed positive exponent, the divisor count is bounded by a constant times that power of the denominator. The proof starts from the prime-power exponent factors, uses unique factorization, and retains all constants. In particular, $\tau(q)^{3/2}\le Dq^{1/12}$ with one fixed positive $D$.
2. **A compatible new rational selection.** Dirichlet approximation constructs a reduced rational $a/q$ with $q\le x^{3/2}$ and $|\theta|\le1/(qx^{3/2})$, where $\theta=\xi-a/q$. The strict error $|\theta|<1/q^2$ is proved as well. Normalization by the rational fractional part preserves the reduced denominator and identifies the exact integer lift of a canonical center.
3. **The complementary full-complement minor argument.** If $q\le\sqrt x$, the effective denominator $T=q(1+|\theta|x^2)$ is at most $2\sqrt x$. Exclusion from all small-denominator lifted source arcs forces $T\ge R/4$. Retaining the divisor loss, the three normalized Ren terms are bounded by

   $$\sqrt2\,x^{-5/24},\qquad x^{-19/120},\qquad 4^{5/12}R^{-5/12}.$$

   The source parameter budget implies $R^4\le x$, so these give a bound of the form $K_{\mathrm{Ren}}(\log x)^d R^{-5/12}$. If $q>\sqrt x$, it lies in the balanced Ghosh range $[\sqrt x,x^{3/2}]$. The fixed choice $\varepsilon=1/16$ gives a normalized saving $x^{-1/16}\le R^{-1/4}$. No fixed epsilon is changed with $N$. Combining the branches proves the alternative full-complement bound

   $$|\widehat{\widetilde A}_{N,\Lambda}(\xi)|
   \le K_{\mathrm{Ren}}(\log(N/2))^d R^{-5/12}+K_{\mathrm{Gh}} R^{-1/4}.$$

   The constants are defined in Lean, and the raw Ren and Ghosh inequalities remain explicit hypotheses. This is a weaker alternative to the stronger printed minor formula in Lemma 6.5; that printed formula is not claimed to be proved or disproved.
4. **Global circle approximation.** Logarithmic losses are absorbed uniformly in $Q$. A complete case split over the exact source rational set and every integer lift combines the major branch with the alternative minor branch. Every circle point is covered through a proved fundamental representative interval. Under the explicit analytic inputs, for every $A\ge0$ and all sufficiently large $N$,

   $$\|E_{Q,N}\|_{\ell^2\to\ell^2}
   \le 2^{A+1}Q^{-1/2}(1+\log N)^{-A}.$$

   The same bound holds for the actual circle error at every frequency. One threshold is chosen before all permitted $Q$ and character/coefficient/beta data.
5. **A true countable maximal error.** The actual dyadic error operators have a summable norm tail. An absolutely convergent positive vector sum is constructed in real $\ell^2$, its coordinate series is identified at every integer, and it is proved to dominate the genuine countable supremum. That supremum is itself realized in $\ell^2$. At a starting dyadic scale $N_0=2^J$, the result is

   $$\left\|\sup_{j\ge0}|E_{Q,2^{J+j}}f|\right\|_2
   \le C_A Q^{-1/2}(1+\log N_0)^{-A}\|f\|_2.$$

   The Q condition is imposed at the starting scale and proved at every larger scale. The character, coefficient and beta data may vary between scales. The supremum covers the entire infinite tail, not only finite truncations.
6. **Continuation and pairing properties.** The actual maximal map is sublinear and Lipschitz. Norm-summable operator outputs vanish in $\ell^2$ and at every integer coordinate, and their maximal tails vanish in $\ell^2$. Exact operator identities identify the error with the actual average minus its circle model. The global error bound also yields finite-indicator pairings bounded by the error norm times $\sqrt{|F||G|}$, with the precise density normalization recorded.

## Explicit inputs and scope

The hypothesis structure `CircleAnalyticInputs` contains beta/coefficient conditions and the following raw deep estimates. It contains no desired approximation or maximal-operator conclusion.

| Input | What remains assumed |
| --- | --- |
| Progression prefix | The actual `progressionMangoldtPrefix` minus `progressionPowerModel` is bounded by $NP\exp(-c\sqrt{\log N})$ for every source denominator, unit residue and real endpoint in $[N/2,N]$. One set of scale data must work throughout that interval. |
| Ren | The displayed three-term estimate for the actual annular positive-phase prime-power sum, with its full $\tau(q)^{3/2}(\log x)^d$ prefactor, at compatible approximants. |
| Ghosh | The displayed fourth-root estimate for the actual quadratic sum at compatible approximants, with fixed $\varepsilon=1/16$, the balanced denominator range and strict reciprocal-square error. |

These published deep estimates are consumed as theorem hypotheses, as authorized. They are not formalized here, added as axioms, or replaced by numerical checks. The scalar constants are fixed before the varying scale, frequency, denominator and input function.

The common permitted range is $Q\ge1$ and

$$\log Q\le\frac{\min(c/7,1)}8\sqrt{\log N}.$$

For a dyadic tail it suffices to impose this condition at its starting scale. Thresholds may depend on the fixed analytic constants and $A$, but not on $Q$ or the later scale data.

The primary estimates were checked against Xiumin Ren's author preprint, [On exponential sum over primes and application in Waring-Goldbach problem](https://www.math.hku.hk/imrwww/IMRPreprintSeries/2004/IMR2004-9.pdf), Theorem 1.1 and equation (1.4). Ghosh's original article is [The Distribution of alpha p squared Modulo 1](https://doi.org/10.1112/plms/s3-42.2.252), Theorem 2; its first-page transcription was also inspected at [this copy](https://www.academia.edu/60387191/The_Distribution_of_p2_Modulo_1). The original Ghosh publisher PDF was inaccessible; Ren's primary text supplies the directly displayed annular estimate. The exact raw inequalities and compatibility hypotheses used in Lean are visible in `RenBalancedInput`, `GhoshBalancedInput` and the consuming modules.

The stronger printed minor estimate of Lemma 6.5 remains open. The complete exceptional-parameter/source correspondence and exact double-sum bridge have not been silently certified by `CircleAnalyticInputs`. The full source version of Lemma 6.9 therefore still needs those bridges, even though the conditional global pointwise/operator approximation for the constructed circle model is proved. Sharp low 6.14, multifrequency 6.16, high/maximal 6.21, Proposition 4.19 and **Theorem 1.1 remain open**. The maximal error estimate above concerns the error component and does not bound the separate high operator.

The ten earlier completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, abstract Theorem 4.1 and abstract Corollary 4.15 under their recorded hypotheses. Lemma 3.21 retains its two earlier explicit PNT limits; the separate PNT project has not been integrated. There is no full-paper correctness or publication-certification claim.

No new manuscript statement error has been established, so no mandatory LaTeX replacement is prescribed. The alternative deduction is fully recorded in the new Lean modules and their expositions. The frozen manuscript and the two accepted revisions remain unchanged.

## Verification

The final checkpoint passes a fresh **3738-job full build of all 213 modules and the root**, with no warnings or errors. All **1104 named theorems** pass a fresh complete transitive axiom audit permitting only `propext`, `Classical.choice` and `Quot.sound`. All **215 project Lean files** pass the source scan: no placeholders, extra mathematical axioms, unchecked evaluation or unsafe code. Import and audit coverage are exact and unique.

The baseline checkpoint 96 source/artifact hashes were verified before continuing. Every new checkpoint compiled its new module and the root and ran complete source and transitive-axiom audits. Unchanged earlier proof sources and compiled artifacts were SHA256 checked before incremental reuse. Checkpoints 121 and 146 performed fresh full project rebuilds. Verification logs and build receipts identify the exact compiled modules and complete dependency history.

Lean 4.34.1 (commit `5045d0056413266e57c625dcd7c365b10e377c52`) and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612` remain pinned. No compiler/kernel modification or version upgrade was made. GitHub CI is configured but has not run on GitHub.

Each checkpoint ZIP is CRC tested, and every archived project file is checked against its SHA256 manifest. Frozen manuscript and accepted revision hashes are checked. These new analytic statements are Lean proofs; no new numerical experiment is used as a substitute. Earlier exact finite experiments and matching script hashes are preserved.

A final download check found 19 truncated archive transfers. Their complete entries were recovered with CRC checks and missing historical logs restored from the retained snapshots. The original file counts and every original Lean source hash were verified against the corresponding build receipts. The archives were replaced under their existing identities and checked again, including their SHA256 manifests. No mathematical proof was changed by this repair. The packaging script now publishes a complete ZIP by atomic rename so that a partially written archive cannot be selected during generation.

## All fifty checkpoints

Each ZIP is a complete project snapshot with its proof notes, logs, source materials and restart instructions. The final ZIP includes all fifty new modules and expositions. Reproducible dependency caches are excluded. Each checkpoint was saved before the following production-tree mutation.

| Checkpoint | Mathematical unit | Added theorems | Project total | Build | Archive and exposition |
| --- | --- | ---: | ---: | --- | --- |
| 97 | A fixed-epsilon Ghosh bound in the balanced denominator range | 5 | 973 | incremental | [ZIP](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint97/PrimeSquares_Checkpoint_97.zip) / [Proof notes](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint97/Checkpoint_97_GhoshBalancedBound.md) |
| 98 | Uniform prime-power exponent growth | 3 | 976 | incremental | [ZIP](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint98/PrimeSquares_Checkpoint_98.zip) / [Proof notes](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint98/Checkpoint_98_ExponentGeometricBound.md) |
| 99 | An unconditional uniform subpower bound for the divisor count | 3 | 979 | incremental | [ZIP](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint99/PrimeSquares_Checkpoint_99.zip) / [Proof notes](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint99/Checkpoint_99_DivisorProductGrowth.md) |
| 100 | A fixed subpower budget for the exact Ren divisor prefactor | 3 | 982 | incremental | [ZIP](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint100/PrimeSquares_Checkpoint_100.zip) / [Proof notes](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint100/Checkpoint_100_RenDivisorBudget.md) |
| 101 | Effective-denominator bounds for the balanced approximation | 3 | 985 | incremental | [ZIP](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint101/PrimeSquares_Checkpoint_101.zip) / [Proof notes](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint101/Checkpoint_101_BalancedEffectiveDenominator.md) |
| 102 | A proved rational selection at balanced precision | 3 | 988 | incremental | [ZIP](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint102/PrimeSquares_Checkpoint_102.zip) / [Proof notes](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint102/Checkpoint_102_BalancedRationalApproximation.md) |
| 103 | The first two normalized Ren terms with the divisor loss retained | 5 | 993 | incremental | [ZIP](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint103/PrimeSquares_Checkpoint_103.zip) / [Proof notes](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint103/Checkpoint_103_RenSmallDenominatorTerms.md) |
| 104 | The inverse effective-denominator term with divisor loss retained | 2 | 995 | incremental | [ZIP](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint104/PrimeSquares_Checkpoint_104.zip) / [Proof notes](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint104/Checkpoint_104_RenInverseEffectiveTerm.md) |
| 105 | The complete weighted Ren bracket in the balanced regime | 3 | 998 | incremental | [ZIP](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint105/PrimeSquares_Checkpoint_105.zip) / [Proof notes](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint105/Checkpoint_105_RenBalancedBracket.md) |
| 106 | The actual annular multiplier under the raw Ren estimate | 2 | 1000 | incremental | [ZIP](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint106/PrimeSquares_Checkpoint_106.zip) / [Proof notes](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint106/Checkpoint_106_AnnularRenBalancedBound.md) |
| 107 | A uniform fourth-power budget for the source scale | 4 | 1004 | incremental | [ZIP](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint107/PrimeSquares_Checkpoint_107.zip) / [Proof notes](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint107/Checkpoint_107_SourceScaleFourthPower.md) |
| 108 | Canonical rational centers for an arbitrary selected approximation | 3 | 1007 | incremental | [ZIP](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint108/PrimeSquares_Checkpoint_108.zip) / [Proof notes](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint108/Checkpoint_108_CanonicalApproximationLift.md) |
| 109 | Exclusion from all lifted source arcs and the effective lower bound | 3 | 1010 | incremental | [ZIP](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint109/PrimeSquares_Checkpoint_109.zip) / [Proof notes](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint109/Checkpoint_109_OutsideSourceArcs.md) |
| 110 | Converting the balanced Ren budget to a scale-only bound | 3 | 1013 | incremental | [ZIP](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint110/PrimeSquares_Checkpoint_110.zip) / [Proof notes](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint110/Checkpoint_110_RenScaleAbsorption.md) |
| 111 | Converting the balanced Ghosh saving to a scale-only bound | 2 | 1015 | incremental | [ZIP](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint111/PrimeSquares_Checkpoint_111.zip) / [Proof notes](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint111/Checkpoint_111_GhoshScaleAbsorption.md) |
| 112 | The small-denominator Ren branch at the actual source scale | 2 | 1017 | incremental | [ZIP](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint112/PrimeSquares_Checkpoint_112.zip) / [Proof notes](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint112/Checkpoint_112_AnnularRenScaleBound.md) |
| 113 | An alternative full-range minor-arc deduction under raw deep estimates | 2 | 1019 | incremental | [ZIP](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint113/PrimeSquares_Checkpoint_113.zip) / [Proof notes](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint113/Checkpoint_113_ComplementaryMinorArcBound.md) |
| 114 | Absorbing fixed logarithmic and power budgets | 3 | 1022 | incremental | [ZIP](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint114/PrimeSquares_Checkpoint_114.zip) / [Proof notes](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint114/Checkpoint_114_LogPowerAbsorption.md) |
| 115 | Uniform logarithmic absorption at the actual source scale | 3 | 1025 | incremental | [ZIP](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint115/PrimeSquares_Checkpoint_115.zip) / [Proof notes](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint115/Checkpoint_115_SourceLogPowerBudget.md) |
| 116 | A uniform source-scale complementary minor budget | 2 | 1027 | incremental | [ZIP](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint116/PrimeSquares_Checkpoint_116.zip) / [Proof notes](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint116/Checkpoint_116_UniformComplementaryBudget.md) |
| 117 | A uniform error bound on the full circle minor-arc complement | 3 | 1030 | incremental | [ZIP](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint117/PrimeSquares_Checkpoint_117.zip) / [Proof notes](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint117/Checkpoint_117_UniformCircleMinorError.md) |
| 118 | The uniform error bound on all lifted major arcs | 2 | 1032 | incremental | [ZIP](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint118/PrimeSquares_Checkpoint_118.zip) / [Proof notes](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint118/Checkpoint_118_WrappedCircleMajorUniform.md) |
| 119 | A conditional global pointwise approximation on the circle | 1 | 1033 | incremental | [ZIP](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint119/PrimeSquares_Checkpoint_119.zip) / [Proof notes](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint119/Checkpoint_119_GlobalCircleApproximation.md) |
| 120 | From a fundamental representative interval to all circle points | 3 | 1036 | incremental | [ZIP](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint120/PrimeSquares_Checkpoint_120.zip) / [Proof notes](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint120/Checkpoint_120_CircleFundamentalBounds.md) |
| 121 | A conditional global approximation for the actual l2 operator | 2 | 1038 | full | [ZIP](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint121/PrimeSquares_Checkpoint_121.zip) / [Proof notes](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint121/Checkpoint_121_CircleApproximationData.md) |
| 122 | Monotonicity of the allowed Q range and source cutoff | 3 | 1041 | incremental | [ZIP](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint122/PrimeSquares_Checkpoint_122.zip) / [Proof notes](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint122/Checkpoint_122_SourceRangeMonotonicity.md) |
| 123 | Exact dyadic logarithms and inverse-power comparison | 4 | 1045 | incremental | [ZIP](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint123/PrimeSquares_Checkpoint_123.zip) / [Proof notes](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint123/Checkpoint_123_DyadicLogarithmicBudget.md) |
| 124 | Quantitative decay of the actual dyadic error operators | 2 | 1047 | incremental | [ZIP](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint124/PrimeSquares_Checkpoint_124.zip) / [Proof notes](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint124/Checkpoint_124_DyadicCircleErrorBudget.md) |
| 125 | A finite reciprocal-square tail with exact telescoping | 3 | 1050 | incremental | [ZIP](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint125/PrimeSquares_Checkpoint_125.zip) / [Proof notes](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint125/Checkpoint_125_ReciprocalSquareFiniteTail.md) |
| 126 | A quantitative infinite reciprocal-square tail | 3 | 1053 | incremental | [ZIP](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint126/PrimeSquares_Checkpoint_126.zip) / [Proof notes](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint126/Checkpoint_126_ReciprocalSquareInfiniteTail.md) |
| 127 | Weighted real-power finite tails | 2 | 1055 | incremental | [ZIP](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint127/PrimeSquares_Checkpoint_127.zip) / [Proof notes](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint127/Checkpoint_127_WeightedPowerFiniteTail.md) |
| 128 | Summability and quantitative weighted infinite tails | 2 | 1057 | incremental | [ZIP](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint128/PrimeSquares_Checkpoint_128.zip) / [Proof notes](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint128/Checkpoint_128_WeightedPowerInfiniteTail.md) |
| 129 | Absolute summability and quantitative tails of operator norms | 3 | 1060 | incremental | [ZIP](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint129/PrimeSquares_Checkpoint_129.zip) / [Proof notes](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint129/Checkpoint_129_OperatorDecaySeries.md) |
| 130 | A genuine countable positive l2 operator envelope | 3 | 1063 | incremental | [ZIP](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint130/PrimeSquares_Checkpoint_130.zip) / [Proof notes](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint130/Checkpoint_130_CountableOperatorEnvelope.md) |
| 131 | Exact coordinate identities for the countable l2 envelope | 3 | 1066 | incremental | [ZIP](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint131/PrimeSquares_Checkpoint_131.zip) / [Proof notes](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint131/Checkpoint_131_CountableEnvelopeCoordinates.md) |
| 132 | Pointwise domination by the countable envelope | 3 | 1069 | incremental | [ZIP](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint132/PrimeSquares_Checkpoint_132.zip) / [Proof notes](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint132/Checkpoint_132_CountableEnvelopeDomination.md) |
| 133 | A bounded true countable maximal function | 4 | 1073 | incremental | [ZIP](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint133/PrimeSquares_Checkpoint_133.zip) / [Proof notes](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint133/Checkpoint_133_CountableOperatorMaximum.md) |
| 134 | A concrete l2 realization of the countable maximal function | 2 | 1075 | incremental | [ZIP](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint134/PrimeSquares_Checkpoint_134.zip) / [Proof notes](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint134/Checkpoint_134_OperatorMaximalMembership.md) |
| 135 | An all-input countable maximal l2 bound | 2 | 1077 | incremental | [ZIP](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint135/PrimeSquares_Checkpoint_135.zip) / [Proof notes](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint135/Checkpoint_135_OperatorMaximalNorm.md) |
| 136 | Sublinearity of the actual countable maximal function | 3 | 1080 | incremental | [ZIP](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint136/PrimeSquares_Checkpoint_136.zip) / [Proof notes](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint136/Checkpoint_136_OperatorMaximalSublinearity.md) |
| 137 | A quantitative countable maximal tail from power decay | 2 | 1082 | incremental | [ZIP](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint137/PrimeSquares_Checkpoint_137.zip) / [Proof notes](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint137/Checkpoint_137_DecayingMaximalTail.md) |
| 138 | Monotonicity of the true countable maximal tails | 3 | 1085 | incremental | [ZIP](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint138/PrimeSquares_Checkpoint_138.zip) / [Proof notes](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint138/Checkpoint_138_MaximalTailMonotonicity.md) |
| 139 | Absolute norm summability of the actual dyadic error family | 1 | 1086 | incremental | [ZIP](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint139/PrimeSquares_Checkpoint_139.zip) / [Proof notes](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint139/Checkpoint_139_DyadicErrorNormSeries.md) |
| 140 | The genuine countable maximal error with a power tail | 1 | 1087 | incremental | [ZIP](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint140/PrimeSquares_Checkpoint_140.zip) / [Proof notes](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint140/Checkpoint_140_DyadicMaximalErrorPower.md) |
| 141 | The conditional logarithmic dyadic maximal error estimate | 3 | 1090 | incremental | [ZIP](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint141/PrimeSquares_Checkpoint_141.zip) / [Proof notes](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint141/Checkpoint_141_DyadicMaximalErrorLog.md) |
| 142 | Vanishing outputs of norm-summable operator families | 3 | 1093 | incremental | [ZIP](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint142/PrimeSquares_Checkpoint_142.zip) / [Proof notes](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint142/Checkpoint_142_SummableOperatorLimits.md) |
| 143 | Vanishing of the genuine countable maximal tails | 2 | 1095 | incremental | [ZIP](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint143/PrimeSquares_Checkpoint_143.zip) / [Proof notes](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint143/Checkpoint_143_MaximalTailVanishing.md) |
| 144 | Identifying the actual average-minus-model maximal error | 3 | 1098 | incremental | [ZIP](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint144/PrimeSquares_Checkpoint_144.zip) / [Proof notes](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint144/Checkpoint_144_DyadicModelDifference.md) |
| 145 | Finite-indicator pairing bounds for the conditional error operator | 3 | 1101 | incremental | [ZIP](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint145/PrimeSquares_Checkpoint_145.zip) / [Proof notes](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint145/Checkpoint_145_QuantitativeErrorPairing.md) |
| 146 | Lipschitz continuity and final verification of the maximal error milestone | 3 | 1104 | full | [ZIP](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint146/PrimeSquares_Checkpoint_146.zip) / [Proof notes](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint146/Checkpoint_146_MaximalErrorLipschitz.md) |

## Continue from checkpoint 147

Recover `PrimeSquares_Checkpoint_146.zip`, verify its archive manifest, and read `STATUS.md`, `docs/CONTINUE_HERE.md`, this report and the relevant individual expositions. The next checkpoint is **147**.

The next mathematical priority is the genuine low-kernel estimate 6.14 and the sharp ordinary/exceptional high and multifrequency inputs 6.16/6.21. Complete the exceptional-data and exact source summation bridges before identifying the constructed model with every printed manuscript object. Then finish Proposition 4.19 and connect Theorem 1.1. The conditional global error, its alternative minor argument and its countable maximal-tail analysis are already complete and should not be repeated. Keep the stronger printed minor formula explicitly open unless a separate proof is supplied.

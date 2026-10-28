# Prime Squares: checkpoints 92–96

Five separately verified checkpoints add **28 named supporting theorems in five modules**. The final project has **163 modules and 968 named supporting theorems**. These are counts of supporting declarations, not counts of completed manuscript results.

The main advance is a proof of the actual periodized circle-model approximation on the major-arc and intermediate-denominator branches, conditional on the explicit progression-prefix estimate. The finite rational indexing and integer shifts are now handled exactly. The full minor-arc range and Theorem 1.1 remain open.

## Saved checkpoints

| Checkpoint | Mathematical unit | Added theorems | Project total | Archive and exposition |
| --- | --- | ---: | ---: | --- |
| 92 | Exact reduced rational index set, including denominator one | 7 | 947 | [ZIP](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint92/PrimeSquares_Checkpoint_92.zip) / [Proof notes](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint92/Checkpoint_92_CanonicalRationalCenters.md) |
| 93 | Separation and uniqueness for every integer lift | 6 | 953 | [ZIP](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint93/PrimeSquares_Checkpoint_93.zip) / [Proof notes](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint93/Checkpoint_93_WrappedRationalArcGeometry.md) |
| 94 | Exact periodization and uniform logarithmic model tails | 8 | 961 | [ZIP](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint94/PrimeSquares_Checkpoint_94.zip) / [Proof notes](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint94/Checkpoint_94_PeriodizedModelTails.md) |
| 95 | Conditional major-arc error for the actual circle model | 4 | 965 | [ZIP](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint95/PrimeSquares_Checkpoint_95.zip) / [Proof notes](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint95/Checkpoint_95_PeriodizedMajorArcError.md) |
| 96 | Conditional intermediate-denominator circle approximation | 3 | 968 | [ZIP](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint96/PrimeSquares_Checkpoint_96.zip) / [Proof notes](sandbox:/workspace/scratch/56a3592766ad/output/checkpoint96/Checkpoint_96_IntermediateCircleApproximation.md) |

Each ZIP contains the complete project at that checkpoint, its proof notes, verification logs, frozen source materials, accepted revisions, dependency pins and continuation notes. Checkpoint 96 includes all five new modules and their expositions. Dependency caches are reproducible and excluded. Earlier checkpoints were saved before the subsequent production-tree changes.

## What the proofs establish

`CanonicalRationalCenters.lean` constructs a finite set with membership exactly equivalent to $0\le r<1$ and $\operatorname{den}(r)\le R$. It accounts for all reduced canonical rationals, the empty zero cutoff, monotonicity and the denominator-one center zero. It does not assert the full character/coefficient summation correspondence with the manuscript.

`WrappedRationalArcGeometry.lean` proves separation of different rational-center/integer-lift pairs, uniqueness of sufficiently narrow arcs, and exclusion of all other lifted arcs. Integer shifts of a real representative give exactly the same point of the circle. Distinct lifts of the same rational are included in the proofs.

`PeriodizedModelTails.lean` writes the genuine periodization exactly as five shifts on the representative interval $[-1,2]$. It proves an outside-arc norm bound of size $O((1+\log R)R^{-5/12})$ for the actual circle model. The fixed constants and budgets are defined in Lean. A common approximation budget is eventually at most $R^{-1/6}$ and has a threshold uniform over $Q\ge1$ at the source scale.

`PeriodizedMajorArcError.lean` bounds the actual circle error on a major arc. The argument retains the four additional shifts of the real model and bounds them using the lifted separation theorem. It includes the shifted copies of the selected center itself. No periodicity is assumed for the continuous real-variable oscillatory integral.

`IntermediateCircleApproximation.lean` treats an approximating denominator $R<q\le R^{11/10}$ on the branch outside every small-denominator lifted major arc. It derives a bound for the actual von Mangoldt multiplier from the progression estimate and unconditional Gauss bounds, then subtracts the actual circle model. The geometric outside-arc condition and existence of the chosen approximation are explicit hypotheses of this branch.

Both conditional approximation branches give

$$\|E_{N,Q}(\xi)\|\le 2^A Q^{-1/2}(1+\log N)^{-A}$$

for all sufficiently large $N$, with one threshold independent of the permitted $Q$ and exceptional data. Here $A\ge0$, $Q\ge1$, $R=\max(\exp((\log N)^{1/10}),Q^8)$, and $\log Q\le\min(c/7,1)\sqrt{\log N}/8$. The relevant lifted arc, coefficient bounds, $0<\beta\le1$ and raw progression-prefix hypotheses remain explicit in the theorem statements.

## Analytic assumptions and open work

The deep input is still a hypothesis bounding the actual `progressionMangoldtPrefix` minus `progressionPowerModel` by $NC\exp(-c\sqrt{\log N})$, for every unit residue and every real endpoint in $[N/2,N]$. The same character, coefficient and beta data are required throughout that interval. This input has not been proved in the project and is not introduced as an axiom. The source-scale inequalities are proved by existing threshold lemmas. The Gauss estimates used in these five units are already proved unconditionally in the project.

The missing range $q>R^{11/10}$ has not been filled by assuming the manuscript's minor-arc conclusion. Full Lemma 6.5, global Lemma 6.9, sharp low 6.14, multifrequency 6.16, high/maximal 6.21, Proposition 4.19 and **Theorem 1.1 remain open**. The full exceptional-parameter/source correspondence is also incomplete. Lemma 3.21 retains its two earlier explicit PNT limits; the separate PNT development has not been integrated by this batch.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, abstract Theorem 4.1 and abstract Corollary 4.15 under their recorded source hypotheses. This batch does not establish a full-paper correctness or publication certification claim.

No new manuscript error has been established. No additional LaTeX replacement is prescribed. The frozen manuscript and the two accepted revisions remain unchanged.

## Verification

The final checkpoint passes a fresh **3682-job full build of all 163 modules and the root**, with no warnings or errors. All **968 named theorems** pass a fresh complete transitive axiom audit allowing only `propext`, `Classical.choice` and `Quot.sound`. All **165 Lean files** pass the source scan: no placeholders, additional mathematical axioms, unchecked evaluation or unsafe code. Import and axiom-audit coverage are exact and unique. Complete output and source/artifact hashes are retained.

Checkpoint 92 also began with a fresh full rebuild after restoring the pinned environment. Checkpoints 93–95 used authenticated dependency-aware builds: earlier proof sources and compiled artifacts were SHA256 checked before reuse, and each new module and the root were compiled. Every checkpoint ran the complete source and transitive-axiom audits. The final full rebuild removes dependence on incremental history for the final verification result.

Lean 4.34.1 (commit `5045d0056413266e57c625dcd7c365b10e377c52`) and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612` remain pinned. All nine dependency revisions were restored exactly. The official Lean archive hash was verified during recovery. The documented process-path compatibility shim does not modify Lean's compiler or kernel. GitHub CI is configured but has not run on GitHub.

Every checkpoint ZIP is CRC tested, and every archived project file is checked against its SHA256 manifest. The frozen manuscript hashes and both accepted revision hashes are checked. These new analytic results are Lean proofs; no new numerical experiment is used as a substitute. Earlier exact finite experiments and their script hashes are preserved.

## Resume

Start from `PrimeSquares_Checkpoint_96.zip`, verify its manifest, and read `STATUS.md`, `docs/CONTINUE_HERE.md` and the five new expositions. The next checkpoint is **97**.

The next mathematical priority is the large-denominator/full-range minor-arc deduction. Check the exact uniform range and constants in a primary-source estimate before using it; do not vary a fixed epsilon with N or assume an uncontrolled own-paper conclusion. Then complete global approximation, connect the exceptional data and prove the sharp operator estimates needed for Proposition 4.19 and Theorem 1.1. The conditional major/intermediate circle branches and earlier exact operator assembly are already complete and should not be repeated.

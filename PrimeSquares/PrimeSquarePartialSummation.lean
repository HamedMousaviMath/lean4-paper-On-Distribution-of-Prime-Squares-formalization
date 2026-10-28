import PrimeSquares.ExceptionalProgressionDensity
import PrimeSquares.SquareMajorArcAssembly

/-!
# Source-model partial summation and the conditional major-arc deduction

The source densities and integrals are actual functions. Only a bound on
the genuine unweighted progression prefix remains a hypothesis. No
weighted-residue estimate or own-paper analytic lemma is assumed.
-/

open Finset MeasureTheory

namespace PrimeSquares

theorem annularProgressionPowerModel_error_identity {N : ℕ} (hN : 1 ≤ N)
    (q : ℕ) (r : ZMod q) (z : ℂ) {β : ℝ} (hβ : 0 < β) (θ : ℝ) :
    Complex.ofReal ((N : ℝ)⁻¹) *
        squareResidueSum (Ioc (N/2) N) q r ArithmeticFunction.vonMangoldt (θ : PrimeCircle) -
      (q.totient : ℂ)⁻¹ * (annularOscillatoryModel N 1 θ - z * annularOscillatoryModel N β θ) =
      Complex.ofReal ((N : ℝ)⁻¹) *
        (quadraticOscillation θ N * (progressionMangoldtPrefix q r N - progressionPowerModel q z β N) -
        quadraticOscillation θ ((N : ℝ)/2) *
          (progressionMangoldtPrefix q r ((N : ℝ)/2) - progressionPowerModel q z β ((N : ℝ)/2)) -
        ∫ t in Set.Ioc ((N : ℝ)/2) N, quadraticOscillationDerivative θ t *
          (progressionMangoldtPrefix q r t - progressionPowerModel q z β t)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hf : ⌊(N : ℝ)/2⌋₊ = N/2 := Nat.floor_div_eq_div N 2
  have h := squareResidueSum_model_error_identity q r θ (a := (N : ℝ)/2) (b := N)
    (by positivity) (by linarith) (progressionPowerModel q z β) (progressionPowerDensity q z β)
    (annularPowerModel_hasDerivAt hN q z hβ) (annularPowerDensity_intervalIntegrable hN q z β)
  simp only [hf, Nat.floor_natCast] at h
  rw [← progressionPowerDensity_integral hN q z β θ, ← mul_sub, h]

theorem annularProgressionPowerModel_error_bound {N : ℕ} (hN : 1 ≤ N)
    (q : ℕ) (r : ZMod q) (z : ℂ) {β : ℝ} (hβ : 0 < β) (θ : ℝ)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hprefix : ∀ t ∈ Set.Icc ((N : ℝ)/2) N,
      ‖progressionMangoldtPrefix q r t - progressionPowerModel q z β t‖ ≤ (N : ℝ)*δ) :
    ‖Complex.ofReal ((N : ℝ)⁻¹) *
        squareResidueSum (Ioc (N/2) N) q r ArithmeticFunction.vonMangoldt (θ : PrimeCircle) -
      (q.totient : ℂ)⁻¹ * (annularOscillatoryModel N 1 θ - z * annularOscillatoryModel N β θ)‖ ≤
      δ * (2 + 4 * Real.pi * |θ| * (N : ℝ)^2) := by
  have h := annularProgressionModel_error_bound hN q r θ hδ
    (progressionPowerModel q z β) (progressionPowerDensity q z β)
    (annularPowerModel_hasDerivAt hN q z hβ) (annularPowerDensity_intervalIntegrable hN q z β) hprefix
  rwa [progressionPowerDensity_integral hN q z β θ] at h

theorem annularMangoldt_majorArc_from_prefix_bound {N q : ℕ} (hN : 1 ≤ N) [NeZero q]
    (χ : DirichletCharacter ℂ q) (κ : ℂ) {β : ℝ} (hβ : 0 < β)
    (a : ℤ) (θ : ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hprefix : ∀ u : (ZMod q)ˣ, ∀ t ∈ Set.Icc ((N : ℝ)/2) N,
      ‖progressionMangoldtPrefix q u t - progressionPowerModel q (κ * χ u) β t‖ ≤ (N : ℝ)*δ) :
    ‖annularWeightedSquareAverageSymbol N ArithmeticFunction.vonMangoldt
        ((((a : ℝ)/q : ℝ) : PrimeCircle) + (θ : PrimeCircle)) -
      (principalSquareSum q (a : ZMod q) * annularOscillatoryModel N 1 θ -
        twistedSquareSum q χ (a : ZMod q) * (κ * annularOscillatoryModel N β θ))‖ ≤
      (Real.log q + 2 * Real.sqrt N * Real.log N) / N +
        (q.totient : ℝ) * (δ * (2 + 4 * Real.pi * |θ| * (N : ℝ)^2)) := by
  apply annularMangoldt_majorArc_error_bound_uniform hN χ a
    (annularOscillatoryModel N 1 θ) (κ * annularOscillatoryModel N β θ) (θ : PrimeCircle)
  intro u
  have hu := annularProgressionPowerModel_error_bound hN q u (κ * χ u) hβ θ hδ (hprefix u)
  have he : (q.totient : ℂ)⁻¹ *
        (annularOscillatoryModel N 1 θ - (κ * χ u) * annularOscillatoryModel N β θ) =
      (q.totient : ℂ)⁻¹ *
        (annularOscillatoryModel N 1 θ - χ u * (κ * annularOscillatoryModel N β θ)) := by ring
  simpa only [squareResidueModelError, he] using hu

theorem annularMangoldt_ordinary_from_prefix_bound {N q : ℕ} (hN : 1 ≤ N) [NeZero q]
    (a : ℤ) (θ : ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hprefix : ∀ u : (ZMod q)ˣ, ∀ t ∈ Set.Icc ((N : ℝ)/2) N,
      ‖progressionMangoldtPrefix q u t - (q.totient : ℂ)⁻¹ * (t : ℂ)‖ ≤ (N : ℝ)*δ) :
    ‖annularWeightedSquareAverageSymbol N ArithmeticFunction.vonMangoldt
        ((((a : ℝ)/q : ℝ) : PrimeCircle) + (θ : PrimeCircle)) -
        principalSquareSum q (a : ZMod q) * annularOscillatoryModel N 1 θ‖ ≤
      (Real.log q + 2 * Real.sqrt N * Real.log N) / N +
        (q.totient : ℝ) * (δ * (2 + 4 * Real.pi * |θ| * (N : ℝ)^2)) := by
  have hp : ∀ u : (ZMod q)ˣ, ∀ t ∈ Set.Icc ((N : ℝ)/2) N,
      ‖progressionMangoldtPrefix q u t - progressionPowerModel q (0 * (1 : DirichletCharacter ℂ q) u) 1 t‖ ≤
        (N : ℝ)*δ := by
    intro u t ht
    simpa only [zero_mul, progressionPowerModel_zero] using hprefix u t ht
  have h := annularMangoldt_majorArc_from_prefix_bound hN (1 : DirichletCharacter ℂ q) 0
    (β := 1) (by norm_num) a θ hδ hp
  simpa only [zero_mul, mul_zero, sub_zero] using h

end PrimeSquares

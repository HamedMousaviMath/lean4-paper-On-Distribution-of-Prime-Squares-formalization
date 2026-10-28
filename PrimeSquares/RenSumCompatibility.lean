import PrimeSquares.QuadraticOscillation

open Finset

namespace PrimeSquares

noncomputable def renQuadraticSum (x ξ : ℝ) : ℂ :=
  ∑ n ∈ Ioc ⌊x⌋₊ ⌊2*x⌋₊,
    (ArithmeticFunction.vonMangoldt n : ℂ) * quadraticOscillation (-ξ) n

theorem renQuadraticSum_exp (x ξ : ℝ) :
    renQuadraticSum x ξ = ∑ n ∈ Ioc ⌊x⌋₊ ⌊2*x⌋₊,
      (ArithmeticFunction.vonMangoldt n : ℂ) *
        Complex.exp (Complex.ofReal (2 * Real.pi * ξ * (n : ℝ)^2) * Complex.I) := by
  unfold renQuadraticSum
  apply sum_congr rfl
  intro n hn
  congr 1
  unfold quadraticOscillation
  congr 2
  push_cast
  ring

theorem quadraticOscillation_neg_conj (ξ t : ℝ) :
    quadraticOscillation (-ξ) t = (starRingEnd ℂ) (quadraticOscillation ξ t) := by
  unfold quadraticOscillation
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

theorem renQuadraticSum_neg_conj (x ξ : ℝ) :
    renQuadraticSum x (-ξ) = (starRingEnd ℂ) (renQuadraticSum x ξ) := by
  simp only [renQuadraticSum, map_sum, map_mul, Complex.conj_ofReal,
    ← quadraticOscillation_neg_conj, neg_neg]

theorem renQuadraticSum_norm_neg (x ξ : ℝ) :
    ‖renQuadraticSum x (-ξ)‖ = ‖renQuadraticSum x ξ‖ := by
  rw [renQuadraticSum_neg_conj, Complex.norm_conj]

theorem annularMangoldtSymbol_eq_Ren (N : ℕ) (ξ : ℝ) :
    annularWeightedSquareAverageSymbol N ArithmeticFunction.vonMangoldt (ξ : PrimeCircle) =
      Complex.ofReal ((N : ℝ)⁻¹) * renQuadraticSum ((N : ℝ)/2) (-ξ) := by
  have hf : ⌊(N : ℝ)/2⌋₊ = N/2 := Nat.floor_div_eq_div N 2
  have he : 2*((N : ℝ)/2) = (N : ℝ) := by ring
  rw [annularWeightedSquareAverageSymbol, finiteSquareSymbol_apply, renQuadraticSum]
  simp only [hf, he, Nat.floor_natCast, neg_neg]
  simp_rw [quadraticOscillation_nat]

theorem annularMangoldtSymbol_norm_Ren (N : ℕ) (ξ : ℝ) :
    ‖annularWeightedSquareAverageSymbol N ArithmeticFunction.vonMangoldt (ξ : PrimeCircle)‖ =
      (N : ℝ)⁻¹ * ‖renQuadraticSum ((N : ℝ)/2) ξ‖ := by
  rw [annularMangoldtSymbol_eq_Ren, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg N)), renQuadraticSum_norm_neg]

end PrimeSquares

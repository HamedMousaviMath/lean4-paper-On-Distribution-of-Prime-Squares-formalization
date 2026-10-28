import PrimeSquares.RationalGaussSmoothMainBlock
namespace PrimeSquares
theorem rationalSmoothMain_coefficient_bound {N : ℕ} (hN : 2 ≤ N)
    (χ : ∀ r : ℚ,DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) {β : ℝ} (hβ : β ≤ 1) (r : ℚ)
    {A₀ A₁ : ℝ} (hp : ‖rationalPrincipalGauss r‖ ≤ A₀)
    (he : ‖rationalExceptionalCoefficient χ κ r‖ ≤ A₁) :
    ‖rationalPrincipalGauss r*annularOscillatoryModel N 1 0-
      rationalExceptionalCoefficient χ κ r*annularOscillatoryModel N β 0‖ ≤ (A₀+A₁)/2 := by
  have hA₀ : 0 ≤ A₀ := (norm_nonneg _).trans hp
  have hA₁ : 0 ≤ A₁ := (norm_nonneg _).trans he
  calc
    _ ≤ ‖rationalPrincipalGauss r*annularOscillatoryModel N 1 0‖+
      ‖rationalExceptionalCoefficient χ κ r*annularOscillatoryModel N β 0‖ := norm_sub_le _ _
    _ ≤ A₀*(1/2 : ℝ)+A₁*(1/2 : ℝ) := by
      rw [norm_mul,norm_mul]
      exact add_le_add (mul_le_mul hp (annularOscillatoryModel_norm_half hN le_rfl 0) (norm_nonneg _) hA₀)
        (mul_le_mul he (annularOscillatoryModel_norm_half hN hβ 0) (norm_nonneg _) hA₁)
    _ = _ := by ring
end PrimeSquares

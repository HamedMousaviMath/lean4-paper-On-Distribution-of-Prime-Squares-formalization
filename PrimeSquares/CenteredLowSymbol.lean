import PrimeSquares.LowModelContinuity
import PrimeSquares.CenteredRationalSymbol

namespace PrimeSquares

theorem sourceArcCutoffScale_zero_of_unit (s : ℕ) {θ : ℝ} (hθ : 1 ≤ |θ|) :
    sourceArcCutoffScale s θ = 0 := by
  apply sourceArcCutoff_zero
  rw [abs_mul,abs_of_pos (by positivity : (0 : ℝ) < (16 : ℝ)^s)]
  have hp : (1 : ℝ) ≤ (16 : ℝ)^s := one_le_pow₀ (by norm_num)
  nlinarith

noncomputable def centeredLowSymbol (N : ℕ) (hN : 1 ≤ N) (q₀ : ℕ) (Q B₀ : ℝ)
    (χ : ∀ r : ℚ, DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β : ℝ) (r : ℚ) : C(ℝ, ℂ) :=
  ⟨fun θ => rationalLowModelTerm N q₀ Q B₀ χ κ β r (θ+(r : ℝ))*
      Complex.ofReal (sourceArcCutoffScale (Nat.log2 r.den) θ),
    ((rationalLowModelTerm_continuous hN q₀ Q B₀ χ κ β r).comp
      (continuous_id.add continuous_const)).mul
      (Complex.continuous_ofReal.comp (sourceArcCutoff_contDiff.continuous.comp
        (continuous_const.mul continuous_id)))⟩

theorem centeredLowSymbol_support (N : ℕ) (hN : 1 ≤ N) (q₀ : ℕ) (Q B₀ : ℝ)
    (χ : ∀ r : ℚ, DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β : ℝ) (r : ℚ)
    (θ : ℝ) (hθ : 1 ≤ |θ|) : centeredLowSymbol N hN q₀ Q B₀ χ κ β r θ = 0 := by
  simp only [centeredLowSymbol,ContinuousMap.coe_mk,sourceArcCutoffScale_zero_of_unit _ hθ,
    Complex.ofReal_zero,mul_zero]

end PrimeSquares

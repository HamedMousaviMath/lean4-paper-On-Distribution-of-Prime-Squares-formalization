import PrimeSquares.RationalExceptionalCoefficientDecay
import PrimeSquares.SourceDyadicDenominatorBounds
namespace PrimeSquares
theorem sourceDyadicGaussCoefficient_envelope {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1/2) :
    ∃ C : ℝ,0 < C ∧ ∀ (s : ℕ) (r : ℚ),r ∈ sourceDyadicRationalCenters s →
      ∀ (χ : ∀ a : ℚ,DirichletCharacter ℂ a.den) (κ : ℚ → ℂ),‖κ r‖ ≤ 1 →
        ‖rationalPrincipalGauss r‖ ≤ C*((2 : ℝ)^s)^(-δ) ∧
        ‖rationalExceptionalCoefficient χ κ r‖ ≤ C*((2 : ℝ)^s)^(-δ) := by
  obtain ⟨C,hC,h⟩ := rationalGaussCoefficient_uniform_decay hδ1
  refine ⟨C,hC,?_⟩
  intro s r hr χ κ hκ
  have hb : (r.den : ℝ)^(-δ) ≤ ((2 : ℝ)^s)^(-δ) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (sourceDyadicRationalCenters_den_bounds hr).1 (by linarith)
  have he := mul_le_mul_of_nonneg_left hb hC.le
  exact ⟨((h χ κ r hκ).1).trans he,((h χ κ r hκ).2).trans he⟩
end PrimeSquares

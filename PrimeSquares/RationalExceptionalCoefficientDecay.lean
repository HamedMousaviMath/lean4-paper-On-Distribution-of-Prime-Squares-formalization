import PrimeSquares.CenteredGaussAnnularDecomposition
namespace PrimeSquares
theorem rationalGaussCoefficient_uniform_decay {δ : ℝ} (hδ : δ < 1/2) :
    ∃ C : ℝ,0 < C ∧ ∀ (χ : ∀ r : ℚ,DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (r : ℚ),
      ‖κ r‖ ≤ 1 → ‖rationalPrincipalGauss r‖ ≤ C*(r.den : ℝ)^(-δ) ∧
        ‖rationalExceptionalCoefficient χ κ r‖ ≤ C*(r.den : ℝ)^(-δ) := by
  obtain ⟨C,hC,h⟩ := rationalGauss_uniform_decay hδ
  refine ⟨C,hC,?_⟩
  intro χ κ r hκ
  refine ⟨(h r).1,?_⟩
  have ht := (h r).2 (χ r)
  change ‖rationalTwistedGauss r (χ r)*κ r‖ ≤ C*(r.den : ℝ)^(-δ)
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_left hκ (norm_nonneg _)).trans (by simpa only [mul_one] using ht)
end PrimeSquares

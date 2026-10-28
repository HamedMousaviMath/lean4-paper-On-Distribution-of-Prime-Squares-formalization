import PrimeSquares.CenteredGaussAnnularDecomposition
namespace PrimeSquares
theorem rationalGaussCoefficient_unit_bounds (χ : ∀ r : ℚ,DirichletCharacter ℂ r.den)
    (κ : ℚ → ℂ) (r : ℚ) (hκ : ‖κ r‖ ≤ 1) :
    ‖rationalPrincipalGauss r‖ ≤ 1 ∧ ‖rationalExceptionalCoefficient χ κ r‖ ≤ 1 := by
  have : NeZero r.den := ⟨r.den_pos.ne'⟩
  refine ⟨norm_principalSquareSum_le_one r.den _,?_⟩
  change ‖twistedSquareSum r.den (χ r) (r.num : ZMod r.den)*κ r‖ ≤ 1
  rw [norm_mul]
  simpa only [one_mul] using mul_le_mul (norm_twistedSquareSum_le_one r.den (χ r) _) hκ
    (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
end PrimeSquares

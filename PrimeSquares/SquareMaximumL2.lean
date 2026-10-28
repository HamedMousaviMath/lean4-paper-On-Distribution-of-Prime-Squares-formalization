import PrimeSquares.SquareMaximumValue

open scoped lp
namespace PrimeSquares

theorem squareMaximumValue_mem_l2 (F : ℕ → ℓ²(ℤ, ℂ)) (hF : Summable (fun j : ℕ => ‖F j‖^2)) :
    Memℓp (squareMaximumValue F) 2 := by
  apply (squareFunctionL2 F hF).2.mono
  intro x
  rw [Real.norm_eq_abs,abs_of_nonneg (squareMaximumValue_nonneg F hF x)]
  exact squareMaximumValue_le_squareFunction F hF x

noncomputable def squareMaximumL2 (F : ℕ → ℓ²(ℤ, ℂ)) (hF : Summable (fun j : ℕ => ‖F j‖^2)) : lp (fun _ : ℤ => ℝ) 2 :=
  ⟨squareMaximumValue F,squareMaximumValue_mem_l2 F hF⟩

theorem squareMaximumL2_norm (F : ℕ → ℓ²(ℤ, ℂ)) (hF : Summable (fun j : ℕ => ‖F j‖^2)) :
    ‖squareMaximumL2 F hF‖ ≤ Real.sqrt (∑' j : ℕ,‖F j‖^2) := by
  rw [←squareFunctionL2_norm F hF]
  apply lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0)
  intro x
  change ‖squareMaximumValue F x‖ ≤ ‖squareFunctionValue F x‖
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (squareMaximumValue_nonneg F hF x),
    abs_of_nonneg (squareFunctionValue_nonneg F x)]
  exact squareMaximumValue_le_squareFunction F hF x

end PrimeSquares

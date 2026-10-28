import PrimeSquares.SquareFunctionValue

open scoped lp
namespace PrimeSquares

theorem squareFunctionValue_mem_l2 (F : ℕ → ℓ²(ℤ, ℂ)) (hF : Summable (fun j : ℕ => ‖F j‖^2)) :
    Memℓp (squareFunctionValue F) 2 := by
  apply (memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)).mpr
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two,Real.norm_eq_abs,sq_abs,squareFunctionValue_sq] using
    coordinate_square_totals_summable F hF

noncomputable def squareFunctionL2 (F : ℕ → ℓ²(ℤ, ℂ)) (hF : Summable (fun j : ℕ => ‖F j‖^2)) : lp (fun _ : ℤ => ℝ) 2 :=
  ⟨squareFunctionValue F,squareFunctionValue_mem_l2 F hF⟩

end PrimeSquares

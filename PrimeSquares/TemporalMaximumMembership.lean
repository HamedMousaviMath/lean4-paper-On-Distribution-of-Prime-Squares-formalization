import PrimeSquares.TemporalMaximumFiniteSpatialEnergy
open scoped lp
namespace PrimeSquares
theorem temporalMaximum_mem_l2 (F : ℕ → ℓ²(ℤ,ℂ)) {B : ℝ} (hB : 0 ≤ B)
    (hF : FiniteTemporalMajorants F B) : Memℓp (fun x : ℤ => ⨆ j : ℕ,‖F j x‖) 2 := by
  apply (memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)).mpr
  simp only [ENNReal.toReal_ofNat,Real.rpow_two,Real.norm_eq_abs,sq_abs]
  exact summable_of_sum_le (fun x => sq_nonneg _) (temporalMaximum_finite_spatial_energy F hB hF)
noncomputable def temporalMaximumL2 (F : ℕ → ℓ²(ℤ,ℂ)) {B : ℝ} (hB : 0 ≤ B)
    (hF : FiniteTemporalMajorants F B) : lp (fun _ : ℤ => ℝ) 2 :=
  ⟨fun x => ⨆ j : ℕ,‖F j x‖,temporalMaximum_mem_l2 F hB hF⟩
end PrimeSquares

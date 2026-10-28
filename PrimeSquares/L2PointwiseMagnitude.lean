import PrimeSquares.BinaryPrefixPointwiseEnvelope
open scoped lp
namespace PrimeSquares
noncomputable def l2Magnitude (f : ℓ²(ℤ,ℂ)) : lp (fun _ : ℤ => ℝ) 2 :=
  ⟨fun x => ‖f x‖,by
    apply (memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)).mpr
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)] using (l2_square_hasSum f).summable⟩
theorem l2Magnitude_norm (f : ℓ²(ℤ,ℂ)) : ‖l2Magnitude f‖=‖f‖ := by
  have hh := lp.norm_rpow_eq_tsum (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal) (l2Magnitude f)
  have he : ‖l2Magnitude f‖^2=‖f‖^2 := by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two,l2Magnitude,Real.norm_eq_abs,sq_abs,l2_square_tsum] using hh
  nlinarith [norm_nonneg (l2Magnitude f),norm_nonneg f]
end PrimeSquares

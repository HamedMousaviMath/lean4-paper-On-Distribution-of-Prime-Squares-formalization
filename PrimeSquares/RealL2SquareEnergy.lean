import PrimeSquares.PrefixMajorantFinitePairing
open scoped lp
namespace PrimeSquares
theorem real_l2_square_summable (g : lp (fun _ : ℤ => ℝ) 2) : Summable (fun x : ℤ => (g x)^2) := by
  have hs := (memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)).mp g.2
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two,Real.norm_eq_abs,sq_abs] using hs
theorem real_l2_square_total (g : lp (fun _ : ℤ => ℝ) 2) : (∑' x : ℤ,(g x)^2)=‖g‖^2 := by
  have hn := lp.norm_rpow_eq_tsum (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal) g
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two,Real.norm_eq_abs,sq_abs] using hn.symm
end PrimeSquares

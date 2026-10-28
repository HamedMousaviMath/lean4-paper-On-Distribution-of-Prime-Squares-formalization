import PrimeSquares.FiniteCircleEnergyAssembly

namespace PrimeSquares

theorem dyadic_denominator_real_lower {r : ℚ} {s : ℕ} (hlog : Nat.log2 r.den=s) :
    (2 : ℝ)^s ≤ r.den := by
  have hh : (2 : ℕ)^s ≤ r.den := by simpa only [hlog] using Nat.log2_self_le r.den_pos.ne'
  exact_mod_cast hh

theorem dyadic_coefficient_power_budget {r : ℚ} {s : ℕ} (hlog : Nat.log2 r.den=s)
    {C δ : ℝ} (hC : 0 ≤ C) (hδ : 0 ≤ δ) (c : ℂ) (hc : ‖c‖ ≤ C*(r.den : ℝ)^(-δ)) :
    ‖c‖ ≤ C*((2 : ℝ)^s)^(-δ) := by
  exact hc.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos
    (pow_pos (by norm_num : (0 : ℝ) < 2) s) (dyadic_denominator_real_lower hlog) (neg_nonpos.mpr hδ)) hC)

end PrimeSquares

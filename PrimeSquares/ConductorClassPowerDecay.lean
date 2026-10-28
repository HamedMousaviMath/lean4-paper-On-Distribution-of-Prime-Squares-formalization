import PrimeSquares.ConductorClassPositivity
namespace PrimeSquares
theorem conductor_class_power_decay {ε : ℝ} (hε : 0 ≤ ε) (q₀ : ℕ → ℕ)
    (hclass : ∀ i,2^i ≤ q₀ i) (i : ℕ) : (q₀ i : ℝ)^(-ε) ≤ ((2 : ℝ)^(-ε))^i := by
  calc
    _ ≤ ((2 : ℝ)^i)^(-ε) := Real.rpow_le_rpow_of_nonpos (by positivity)
      (conductor_class_real_lower q₀ hclass i) (neg_nonpos.mpr hε)
    _ = _ := by rw [←Real.rpow_natCast_mul (by norm_num),mul_comm,Real.rpow_mul_natCast (by norm_num)]
end PrimeSquares

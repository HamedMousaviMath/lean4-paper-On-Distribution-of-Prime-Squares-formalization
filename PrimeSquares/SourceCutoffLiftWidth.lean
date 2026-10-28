import PrimeSquares.SourceArcCutoff
namespace PrimeSquares
theorem source_cutoff_lift_width {s : ℕ} (hs : 1 ≤ s) : 2*(1/(16 : ℝ)^s)<1 := by
  have hn : 16 ≤ 16^s := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by norm_num : 0<16) hs
  have hp : (16 : ℝ) ≤ (16 : ℝ)^s := by exact_mod_cast hn
  rw [mul_one_div]
  exact (div_lt_iff₀ (by positivity)).mpr (by linarith)
end PrimeSquares

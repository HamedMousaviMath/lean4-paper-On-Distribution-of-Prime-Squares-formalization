import PrimeSquares.RealIWParameters

set_option autoImplicit false
namespace PrimeSquares

theorem quadratic_log_loss_not_linear (K : ℝ) :
    ∃ s : ℕ,K*(1+(s:ℝ)) < (1+(s:ℝ))^2 := by
  refine ⟨⌈K⌉₊+1,?_⟩
  have h := Nat.le_ceil K
  have hN : (0:ℝ)≤⌈K⌉₊ := Nat.cast_nonneg _
  push_cast
  nlinarith

theorem cubic_log_loss_not_quadratic (K : ℝ) :
    ∃ s : ℕ,K*(1+(s:ℝ))^2 < (1+(s:ℝ))^3 := by
  obtain ⟨s,hs⟩ := quadratic_log_loss_not_linear K
  have hpos : 0 < 1+(s:ℝ) := by positivity
  have h := mul_lt_mul_of_pos_right hs hpos
  refine ⟨s,?_⟩
  convert h using 1 <;> ring

noncomputable def densityProfileSpike (a b : ℝ) : ℝ := if a=1 ∧ b=1 then 1 else 0

theorem densityProfileSpike_nonneg (a b : ℝ) : 0 ≤ densityProfileSpike a b := by
  unfold densityProfileSpike
  split_ifs <;> norm_num

theorem densityProfileSpike_no_dilation_comparison {D : ℝ} (hD : 1 < D) (K : ℝ) :
    K*densityProfileSpike (1/D) (1/D) < densityProfileSpike 1 1 := by
  have hDne : D ≠ 1 := ne_of_gt hD
  norm_num [densityProfileSpike,one_div,inv_eq_one,hDne]

end PrimeSquares

import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring

namespace PrimeSquares

noncomputable def schwartzDecayConstant (f : SchwartzMap ℝ ℂ) (K : ℕ) : ℝ :=
  2^K*(SchwartzMap.seminorm ℝ 0 0 f+SchwartzMap.seminorm ℝ K 0 f)

theorem schwartzDecayConstant_nonneg (f : SchwartzMap ℝ ℂ) (K : ℕ) :
    0 ≤ schwartzDecayConstant f K := by
  unfold schwartzDecayConstant
  exact mul_nonneg (by positivity) (add_nonneg (apply_nonneg _ _) (apply_nonneg _ _))

theorem schwartz_polynomial_decay (f : SchwartzMap ℝ ℂ) (K : ℕ) (x : ℝ) :
    (1+|x|)^K*‖f x‖ ≤ schwartzDecayConstant f K := by
  have h0 := SchwartzMap.norm_le_seminorm ℝ f x
  have hK := SchwartzMap.norm_pow_mul_le_seminorm ℝ f K x
  rw [Real.norm_eq_abs] at hK
  have hs0 : 0 ≤ SchwartzMap.seminorm ℝ 0 0 f := apply_nonneg _ _
  have hsK : 0 ≤ SchwartzMap.seminorm ℝ K 0 f := apply_nonneg _ _
  unfold schwartzDecayConstant
  by_cases hx : |x| ≤ 1
  · have hp : (1+|x|)^K ≤ (2 : ℝ)^K := pow_le_pow_left₀ (by positivity) (by linarith) K
    have hm := mul_le_mul hp h0 (norm_nonneg _) (by positivity : (0 : ℝ) ≤ (2 : ℝ)^K)
    nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ (2 : ℝ)^K) hsK]
  · have hx' : 1 ≤ |x| := le_of_lt (lt_of_not_ge hx)
    have hp : (1+|x|)^K ≤ (2*|x|)^K := pow_le_pow_left₀ (by positivity) (by linarith) K
    rw [mul_pow] at hp
    calc
      _ ≤ (2^K*|x|^K)*‖f x‖ := mul_le_mul_of_nonneg_right hp (norm_nonneg _)
      _ = 2^K*(|x|^K*‖f x‖) := by ring
      _ ≤ 2^K*SchwartzMap.seminorm ℝ K 0 f := mul_le_mul_of_nonneg_left hK (by positivity)
      _ ≤ _ := by gcongr;linarith

end PrimeSquares

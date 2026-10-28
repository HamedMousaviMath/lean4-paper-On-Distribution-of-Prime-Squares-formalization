import PrimeSquares.QuadraticOscillation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
namespace PrimeSquares
theorem quadraticOscillation_sub_one_norm (θ t : ℝ) :
    ‖quadraticOscillation θ t-1‖ ≤ 2*Real.pi*|θ| *t^2 := by
  have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := -2*Real.pi*θ*t^2)
  have he : ‖(-2*Real.pi*θ*t^2 : ℝ)‖=2*Real.pi*|θ| *t^2 := by
    simp only [Real.norm_eq_abs,abs_mul,abs_of_nonneg (sq_nonneg t),abs_of_pos Real.pi_pos]
    norm_num
  rw [he] at h
  simpa only [quadraticOscillation,mul_comm Complex.I] using h
end PrimeSquares

import PrimeSquares.QuadraticPhaseSmallFrequency
import PrimeSquares.AnnularModelSize
namespace PrimeSquares
theorem annularDifference_integrand_bound {N : ℕ} (hN : 2 ≤ N) {β : ℝ} (hβ : β ≤ 1)
    (θ : ℝ) {t : ℝ} (ht : t ∈ Set.Icc ((N : ℝ)/2) N) :
    ‖Complex.ofReal (t^(β-1))*(quadraticOscillation θ t-1)‖ ≤ 2*Real.pi*|θ| *(N : ℝ)^2 := by
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have ht0 : 0 ≤ t := by linarith [ht.1]
  have hd : t^(β-1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith [ht.1]) (by linarith)
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg ht0 _)]
  calc
    _ ≤ 1*‖quadraticOscillation θ t-1‖ := mul_le_mul_of_nonneg_right hd (norm_nonneg _)
    _ ≤ 2*Real.pi*|θ| *t^2 := by simpa only [one_mul] using quadraticOscillation_sub_one_norm θ t
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht0 ht.2 2) (by positivity)
end PrimeSquares

import PrimeSquares.ScaledCutoffKernel

namespace PrimeSquares

theorem decayProfile_mono_scale {a H : ℝ} (ha : 0 < a) (haH : a ≤ H) (K : ℕ) (x : ℝ) :
    decayProfile a K x ≤ decayProfile H K x := by
  have hH : 0 < H := ha.trans_le haH
  have hd : |x|/H ≤ |x|/a := div_le_div_of_nonneg_left (abs_nonneg _) ha haH
  unfold decayProfile
  exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) (by linarith) K)

theorem scaledCutoffKernel_larger_profile {a H : ℝ} (ha : 0 < a) (haH : a ≤ H)
    (K : ℕ) (x : ℝ) :
    ‖scaledCutoffKernel a x‖ ≤ cutoffDecayConstant K/a*decayProfile H K x := by
  exact (scaledCutoffKernel_decay ha K x).trans
    (mul_le_mul_of_nonneg_left (decayProfile_mono_scale ha haH K x)
      (div_nonneg (cutoffDecayConstant_nonneg K) ha.le))

end PrimeSquares

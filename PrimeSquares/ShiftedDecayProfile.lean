import PrimeSquares.DecayProfile

namespace PrimeSquares

theorem decayProfile_shift_base {H C x y : ℝ} (hH : 0 < H) (hC : 0 ≤ C)
    (hy : |y| ≤ C*H) :
    1+|x|/H ≤ (1+C)*(1+|x-y|/H) := by
  have ht : |x| ≤ |x-y|+|y| := by simpa using (abs_add_le (x-y) y)
  have hr : |y|/H ≤ C := (div_le_iff₀ hH).mpr hy
  have hs : |x|/H ≤ |x-y|/H+|y|/H := by
    rw [←add_div];exact div_le_div_of_nonneg_right ht hH.le
  have hd : 0 ≤ |x-y|/H := div_nonneg (abs_nonneg _) hH.le
  nlinarith [mul_nonneg hC hd]

theorem decayProfile_shift_bound {H C x y : ℝ} (hH : 0 < H) (hC : 0 ≤ C)
    (hy : |y| ≤ C*H) (K : ℕ) :
    decayProfile H K (x-y) ≤ (1+C)^K*decayProfile H K x := by
  have hx : 0 < (1+|x|/H)^K := by positivity
  have hz : 0 < (1+|x-y|/H)^K := by positivity
  have h := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1+|x|/H)
    (decayProfile_shift_base hH hC hy) K
  rw [mul_pow] at h
  unfold decayProfile
  apply (le_div_iff₀ hx).mpr
  have hd : (1+|x|/H)^K/(1+|x-y|/H)^K ≤ (1+C)^K := (div_le_iff₀ hz).mpr h
  convert hd using 1; ring

end PrimeSquares

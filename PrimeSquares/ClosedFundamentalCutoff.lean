import PrimeSquares.CompactCirclePeriodization
import PrimeSquares.CompactCircleCore

namespace PrimeSquares

theorem compactCircleLift_small_support_closed (f : C(ℝ, ℂ))
    (hs : ∀ ξ : ℝ,1 ≤ |ξ| → f ξ=0) (hn : ∀ ξ : ℝ,1/2 ≤ |ξ| → f ξ=0)
    {ξ : ℝ} (hξ : ξ ∈ Set.Icc (-(1/2) : ℝ) (1/2)) :
    compactCircleLift f hs (ξ : PrimeCircle)=f ξ := by
  rw [compactCircleLift_all_real]
  have hz : ∀ k : ℤ,k ≠ 0 → f (ξ+k)=0 := by
    intro k hk
    apply hn
    have hk' : k ≤ -1 ∨ 1 ≤ k := by omega
    rcases hk' with hk' | hk'
    · have hkr : (k : ℝ) ≤ -1 := by exact_mod_cast hk'
      rw [abs_of_nonpos (by linarith [hξ.2])]
      linarith [hξ.2]
    · have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk'
      rw [abs_of_nonneg (by linarith [hξ.1])]
      linarith [hξ.1]

  simpa only [Int.cast_zero,add_zero] using tsum_eq_single 0 hz

end PrimeSquares

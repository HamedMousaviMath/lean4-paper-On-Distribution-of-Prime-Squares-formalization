import PrimeSquares.CompactCircleLift

namespace PrimeSquares

theorem compactPeriodWindow_small_support (f : ℝ → ℂ)
    (hs : ∀ x, 1/2 ≤ |x| → f x = 0) {x : ℝ}
    (hx : x ∈ Set.Icc (-(1/2) : ℝ) (1/2)) :
    compactPeriodWindow f x = f x := by
  have hleft : f (x-1) = 0 := hs _ (by
    rw [abs_of_nonpos (by linarith [hx.2])];linarith [hx.2])
  have hright : f (x+1) = 0 := hs _ (by
    rw [abs_of_nonneg (by linarith [hx.1])];linarith [hx.1])
  simp only [compactPeriodWindow,hleft,hright,zero_add,add_zero]

theorem compactCircleLift_small_support_real (f : C(ℝ, ℂ))
    (hs : ∀ x, 1 ≤ |x| → f x = 0) (hsmall : ∀ x, 1/2 ≤ |x| → f x = 0)
    {x : ℝ} (hx : x ∈ Set.Ico (-(1/2) : ℝ) (1/2)) :
    compactCircleLift f hs (x : PrimeCircle) = f x := by
  rw [compactCircleLift_real f hs hx]
  exact compactPeriodWindow_small_support f hsmall ⟨hx.1,hx.2.le⟩

end PrimeSquares

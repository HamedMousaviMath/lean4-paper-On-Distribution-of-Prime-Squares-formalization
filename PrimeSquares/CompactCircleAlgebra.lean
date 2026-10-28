import PrimeSquares.CompactCircleLift

namespace PrimeSquares

theorem compactCircleLift_add (f g : C(ℝ, ℂ))
    (hf : ∀ x, 1 ≤ |x| → f x = 0) (hg : ∀ x, 1 ≤ |x| → g x = 0)
    (hfg : ∀ x, 1 ≤ |x| → (f+g) x = 0) :
    compactCircleLift (f+g) hfg = compactCircleLift f hf + compactCircleLift g hg := by
  ext θ
  change compactPeriodWindow (f+g) _ = compactPeriodWindow f _ + compactPeriodWindow g _
  simp only [compactPeriodWindow, Pi.add_apply]
  ring

theorem compactCircleLift_smul (c : ℂ) (f : C(ℝ, ℂ))
    (hf : ∀ x, 1 ≤ |x| → f x = 0) (hc : ∀ x, 1 ≤ |x| → (c • f) x = 0) :
    compactCircleLift (c • f) hc = c • compactCircleLift f hf := by
  ext θ
  change compactPeriodWindow (c • f) _ = c * compactPeriodWindow f _
  simp only [compactPeriodWindow, Pi.smul_apply, smul_eq_mul]
  ring

end PrimeSquares

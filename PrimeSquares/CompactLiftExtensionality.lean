import PrimeSquares.CompactLiftSourceAlgebra
import PrimeSquares.CircleShiftAlgebra

namespace PrimeSquares

theorem compactCircleLift_congr (f g : C(ℝ, ℂ))
    (hf : ∀ x,1 ≤ |x| → f x=0) (hg : ∀ x,1 ≤ |x| → g x=0) (h : f=g) :
    compactCircleLift f hf=compactCircleLift g hg := by
  subst g
  rfl

theorem circleFrequencyShift_zero (r : PrimeCircle) : circleFrequencyShift 0 r=0 := by
  ext θ
  rfl

theorem shiftedAnnularLift_smul (N : ℕ) (hN : 1 ≤ N) (β a : ℝ) (ha : 2 ≤ a)
    (c : ℂ) (r : PrimeCircle)
    (hs : ∀ x,1 ≤ |x| → (c • annularCutoffSymbol N hN β a) x=0) :
    circleFrequencyShift (compactCircleLift (c • annularCutoffSymbol N hN β a) hs) r=
      c • circleFrequencyShift (circleAnnularCutoff N hN β a ha) r := by
  erw [compactCircleLift_smul _ _ (annularCutoffSymbol_support N hN β ha) hs]
  rw [circleFrequencyShift_smul]
  rfl

end PrimeSquares

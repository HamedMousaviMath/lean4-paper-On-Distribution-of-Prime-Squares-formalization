import PrimeSquares.SourceLowCircleRealFormula
import PrimeSquares.CompactCircleAlgebra
import PrimeSquares.FourierKernelSums

namespace PrimeSquares

theorem compactCircleLift_zero (hs : ∀ x : ℝ,1 ≤ |x| → (0 : C(ℝ, ℂ)) x=0) :
    compactCircleLift 0 hs=0 := by
  ext θ
  change compactPeriodWindow (0 : C(ℝ, ℂ)) _=0
  simp [compactPeriodWindow]

theorem compactCircleLift_sub (f g : C(ℝ, ℂ))
    (hf : ∀ x,1 ≤ |x| → f x=0) (hg : ∀ x,1 ≤ |x| → g x=0)
    (hfg : ∀ x,1 ≤ |x| → (f-g) x=0) :
    compactCircleLift (f-g) hfg=compactCircleLift f hf-compactCircleLift g hg := by
  ext θ
  change compactPeriodWindow (f-g) _=compactPeriodWindow f _-compactPeriodWindow g _
  simp only [compactPeriodWindow,Pi.sub_apply]
  ring

end PrimeSquares

import PrimeSquares.CircleFrequencyShiftKernel
import PrimeSquares.CompactLiftSourceAlgebra

namespace PrimeSquares

theorem circleFrequencyShift_add (f g : C(PrimeCircle, ℂ)) (r : PrimeCircle) :
    circleFrequencyShift (f+g) r=circleFrequencyShift f r+circleFrequencyShift g r := by
  ext θ
  rfl

theorem circleFrequencyShift_sub (f g : C(PrimeCircle, ℂ)) (r : PrimeCircle) :
    circleFrequencyShift (f-g) r=circleFrequencyShift f r-circleFrequencyShift g r := by
  ext θ
  rfl

theorem circleFrequencyShift_smul (c : ℂ) (f : C(PrimeCircle, ℂ)) (r : PrimeCircle) :
    circleFrequencyShift (c • f) r=c • circleFrequencyShift f r := by
  ext θ
  rfl

end PrimeSquares

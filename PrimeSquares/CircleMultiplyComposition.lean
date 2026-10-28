import PrimeSquares.SourceCollarSubhalfMaximum
open Finset MeasureTheory
open scoped lp
namespace PrimeSquares
theorem circleMultiply_comp_apply (m n : C(PrimeCircle,ℂ)) (f : PrimeCircleL2) :
    circleMultiply m (circleMultiply n f)=circleMultiply (m*n) f := by
  apply Lp.ext
  filter_upwards [circleMultiply_ae m (circleMultiply n f),circleMultiply_ae n f,
    circleMultiply_ae (m*n) f] with θ h1 h2 h3
  rw [h1,h2,h3]
  change m θ*(n θ*f θ)=(m θ*n θ)*f θ
  ring
end PrimeSquares

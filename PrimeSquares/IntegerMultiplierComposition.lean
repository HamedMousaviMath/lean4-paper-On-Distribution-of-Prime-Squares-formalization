import PrimeSquares.CircleMultiplyComposition
open Finset MeasureTheory
open scoped lp
namespace PrimeSquares
theorem integerMultiplier_comp_apply (m n : C(PrimeCircle,ℂ)) (f : ℓ²(ℤ,ℂ)) :
    integerMultiplier m (integerMultiplier n f)=integerMultiplier (m*n) f := by
  apply integerFourier.injective
  rw [integerFourier_multiplier,integerFourier_multiplier,integerFourier_multiplier,
    circleMultiply_comp_apply]
end PrimeSquares

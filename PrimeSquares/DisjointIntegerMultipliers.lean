import PrimeSquares.CircleDisjointInner
open Finset MeasureTheory
open scoped lp
namespace PrimeSquares
theorem integerMultiplier_disjoint_inner (m n : C(PrimeCircle,ℂ))
    (hmn : ∀ θ,m θ=0 ∨ n θ=0) (f g : ℓ²(ℤ,ℂ)) :
    inner ℂ (integerMultiplier m f) (integerMultiplier n g)=0 := by
  rw [←integerFourier.inner_map_map,integerFourier_multiplier,integerFourier_multiplier]
  exact circleMultiply_disjoint_inner m n hmn _ _
end PrimeSquares

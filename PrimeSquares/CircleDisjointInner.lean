import PrimeSquares.IntegerMultiplierComposition
open Finset MeasureTheory
open scoped lp
namespace PrimeSquares
theorem circleMultiply_disjoint_inner (m n : C(PrimeCircle,ℂ))
    (hmn : ∀ θ,m θ=0 ∨ n θ=0) (f g : PrimeCircleL2) :
    inner ℂ (circleMultiply m f) (circleMultiply n g)=0 := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_eq_zero_of_ae
  filter_upwards [circleMultiply_ae m f,circleMultiply_ae n g] with θ hf hg
  rw [hf,hg]
  rcases hmn θ with hm|hn
  · simp [hm]
  · simp [hn]
end PrimeSquares

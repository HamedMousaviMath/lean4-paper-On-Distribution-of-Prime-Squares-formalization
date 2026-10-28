import PrimeSquares.ExceptionalCollarInactive
open Finset
namespace PrimeSquares
theorem time_class_sum (J : Finset ℕ) (σ : ℕ → ℕ) (v : ℕ → ℝ) :
    (∑ j ∈ J,v j)=∑ i ∈ J.image σ,∑ j ∈ J.filter (fun j => σ j=i),v j := by
  exact (sum_fiberwise_of_maps_to (fun j hj => mem_image_of_mem σ hj) v).symm
end PrimeSquares

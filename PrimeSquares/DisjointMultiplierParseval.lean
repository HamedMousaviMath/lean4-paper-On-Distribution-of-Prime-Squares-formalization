import PrimeSquares.DisjointIntegerMultipliers
import PrimeSquares.OrthogonalFiniteSumEnergy
open Finset MeasureTheory
open scoped lp
namespace PrimeSquares
theorem disjointMultiplier_finset_energy (m : ℕ → C(PrimeCircle,ℂ))
    (hm : ∀ i j,i ≠ j → ∀ θ,m i θ=0 ∨ m j θ=0)
    (F : ℕ → ℓ²(ℤ,ℂ)) (S : Finset ℕ) :
    ‖∑ i ∈ S,integerMultiplier (m i) (F i)‖^2=
      ∑ i ∈ S,‖integerMultiplier (m i) (F i)‖^2 := by
  exact orthogonal_finset_sum_energy _
    (fun i j hij => integerMultiplier_disjoint_inner _ _ (hm i j hij) _ _) S
end PrimeSquares

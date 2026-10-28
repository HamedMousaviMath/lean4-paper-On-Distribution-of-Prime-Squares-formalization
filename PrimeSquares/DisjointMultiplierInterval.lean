import PrimeSquares.DisjointMultiplierParseval
import PrimeSquares.OrthogonalL2IntervalEnergy
open Finset MeasureTheory
open scoped lp
namespace PrimeSquares
theorem disjointMultiplier_interval_energy (m : ℕ → C(PrimeCircle,ℂ))
    (hm : ∀ i j,i ≠ j → ∀ θ,m i θ=0 ∨ m j θ=0)
    (F : ℕ → ℓ²(ℤ,ℂ)) (a K : ℕ) :
    ‖intervalL2Sum a K (fun i => integerMultiplier (m i) (F i))‖^2=
      intervalRealBudget a K (fun i => ‖integerMultiplier (m i) (F i)‖^2) := by
  exact orthogonal_l2_interval_energy _
    (fun i j hij => integerMultiplier_disjoint_inner _ _ (hm i j hij) _ _) a K
end PrimeSquares

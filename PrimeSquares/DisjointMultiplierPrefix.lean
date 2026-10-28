import PrimeSquares.DisjointMultiplierInterval
import PrimeSquares.OrthogonalRademacherMenshov
open Finset MeasureTheory
open scoped lp
namespace PrimeSquares
theorem disjointMultiplier_prefix_majorant (h a : ℕ) (m : ℕ → C(PrimeCircle,ℂ))
    (hm : ∀ i j,i ≠ j → ∀ θ,m i θ=0 ∨ m j θ=0) (F : ℕ → ℓ²(ℤ,ℂ)) :
    ∃ g : lp (fun _ : ℤ => ℝ) 2,(∀ x,0 ≤ g x) ∧
      (∀ K,K ≤ 2^h → ∀ x,
        ‖intervalL2Sum a K (fun i => integerMultiplier (m i) (F i)) x‖ ≤ g x) ∧
      ‖g‖ ≤ (h+1 : ℝ)*Real.sqrt (intervalRealBudget a (2^h)
        (fun i => ‖integerMultiplier (m i) (F i)‖^2)) := by
  exact orthogonal_rademacherMenshov h a _
    (fun i j hij => integerMultiplier_disjoint_inner _ _ (hm i j hij) _ _)
end PrimeSquares

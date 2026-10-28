import PrimeSquares.OrthogonalFiniteSumEnergy
import Mathlib.Analysis.InnerProductSpace.l2Space
open scoped lp
namespace PrimeSquares
theorem orthogonal_l2_interval_energy (F : ℕ → ℓ²(ℤ,ℂ))
    (hF : ∀ i j,i ≠ j → inner ℂ (F i) (F j)=0) (a K : ℕ) :
    ‖intervalL2Sum a K F‖^2=intervalRealBudget a K (fun i => ‖F i‖^2) := by
  exact orthogonal_finset_sum_energy (fun i => F (a+i))
    (fun i j hij => hF (a+i) (a+j) (by omega)) (Finset.range K)
end PrimeSquares

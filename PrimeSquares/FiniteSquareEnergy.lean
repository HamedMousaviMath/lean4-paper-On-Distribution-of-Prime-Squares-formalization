import PrimeSquares.SquareMaximumL2

open scoped lp
namespace PrimeSquares

def FiniteSquareEnergyBound (F : ℕ → ℓ²(ℤ, ℂ)) (B : ℝ) : Prop :=
  ∀ S : Finset ℕ,(∑ j ∈ S,‖F j‖^2) ≤ B^2

theorem finiteSquareEnergy_summable (F : ℕ → ℓ²(ℤ, ℂ)) {B : ℝ} (hF : FiniteSquareEnergyBound F B) :
    Summable (fun j : ℕ => ‖F j‖^2) := summable_of_sum_le (fun j => sq_nonneg ‖F j‖) hF

theorem finiteSquareEnergy_total (F : ℕ → ℓ²(ℤ, ℂ)) {B : ℝ} (hF : FiniteSquareEnergyBound F B) :
    (∑' j : ℕ,‖F j‖^2) ≤ B^2 := Real.tsum_le_of_sum_le (fun j => sq_nonneg ‖F j‖) hF

theorem finiteSquareEnergy_maximal (F : ℕ → ℓ²(ℤ, ℂ)) {B : ℝ} (hB : 0 ≤ B) (hF : FiniteSquareEnergyBound F B) :
    ‖squareMaximumL2 F (finiteSquareEnergy_summable F hF)‖ ≤ B := by
  apply (squareMaximumL2_norm F _).trans
  exact (Real.sqrt_le_sqrt (finiteSquareEnergy_total F hF)).trans_eq (Real.sqrt_sq hB)

end PrimeSquares

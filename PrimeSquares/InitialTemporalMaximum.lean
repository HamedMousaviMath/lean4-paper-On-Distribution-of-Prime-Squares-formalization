import PrimeSquares.RealL2SquareEnergy
import Mathlib.Order.PartialSups
open scoped lp
namespace PrimeSquares
noncomputable def initialTemporalMaximum (F : ℕ → ℓ²(ℤ,ℂ)) (n : ℕ) (x : ℤ) : ℝ :=
  partialSups (fun j => ‖F j x‖) n
theorem initialTemporalMaximum_nonneg (F : ℕ → ℓ²(ℤ,ℂ)) (n : ℕ) (x : ℤ) :
    0 ≤ initialTemporalMaximum F n x :=
  (norm_nonneg _).trans (le_partialSups (fun j => ‖F j x‖) n)
theorem initialTemporalMaximum_dominates (F : ℕ → ℓ²(ℤ,ℂ)) {j n : ℕ} (hj : j ≤ n) (x : ℤ) :
    ‖F j x‖ ≤ initialTemporalMaximum F n x :=
  le_partialSups_of_le (fun j => ‖F j x‖) hj
end PrimeSquares

import PrimeSquares.FiniteSymbolLocalization
open Finset MeasureTheory
open scoped lp
namespace PrimeSquares
theorem localized_interval_input_energy (a K : ℕ) (p : ℕ → C(PrimeCircle,ℂ))
    (hp : ∀ i j,i ≠ j → ∀ θ,p i θ=0 ∨ p j θ=0) (f : ℓ²(ℤ,ℂ)) :
    ‖integerMultiplier (intervalCircleSymbol a K p) f‖^2=
      intervalRealBudget a K (fun i => ‖integerMultiplier (p i) f‖^2) := by
  rw [integerMultiplier_interval]
  exact disjointMultiplier_interval_energy p hp (fun _ => f) a K
end PrimeSquares

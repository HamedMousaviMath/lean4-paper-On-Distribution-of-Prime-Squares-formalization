import PrimeSquares.SourceDyadicDenominatorBounds
import PrimeSquares.CircleRationalModelFiniteEnergy
open Finset
open scoped lp
namespace PrimeSquares
theorem sourceDyadic_model_energy {s : ℕ} (hs : 2 ≤ s)
    (N : ℕ) (hN : 1 ≤ N) (χ : ∀ r : ℚ,DirichletCharacter ℂ r.den)
    (κ : ℚ → ℂ) (β : ℝ) (F : ℚ → ℓ²(ℤ,ℂ)) :
    ‖∑ r ∈ sourceDyadicRationalCenters s,integerMultiplier (circleRationalModelTerm N hN χ κ β r) (F r)‖^2=
    ∑ r ∈ sourceDyadicRationalCenters s,‖integerMultiplier (circleRationalModelTerm N hN χ κ β r) (F r)‖^2 :=
  circleRationalModel_finite_energy hs _ (fun r hr => ((mem_sourceDyadicRationalCenters s r).mp hr).1)
    (fun _ hr => (sourceDyadicRationalCenters_den_bounds hr).2.le)
    (fun r hr => ((mem_sourceDyadicRationalCenters s r).mp hr).2) N hN χ κ β F
end PrimeSquares

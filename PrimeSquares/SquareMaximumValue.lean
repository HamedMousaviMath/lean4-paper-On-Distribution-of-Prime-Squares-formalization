import PrimeSquares.SquareFunctionNorm

open scoped lp
namespace PrimeSquares

noncomputable def squareMaximumValue (F : ℕ → ℓ²(ℤ, ℂ)) (x : ℤ) : ℝ := ⨆ j : ℕ,‖F j x‖

theorem squareMaximumValue_bddAbove (F : ℕ → ℓ²(ℤ, ℂ)) (hF : Summable (fun j : ℕ => ‖F j‖^2)) (x : ℤ) :
    BddAbove (Set.range (fun j : ℕ => ‖F j x‖)) :=
  ⟨squareFunctionValue F x,by rintro _ ⟨j,rfl⟩;exact squareFunctionValue_dominates F hF j x⟩

theorem squareMaximumValue_nonneg (F : ℕ → ℓ²(ℤ, ℂ)) (hF : Summable (fun j : ℕ => ‖F j‖^2)) (x : ℤ) :
    0 ≤ squareMaximumValue F x := (norm_nonneg (F 0 x)).trans (le_ciSup (squareMaximumValue_bddAbove F hF x) 0)

theorem squareMaximumValue_le_squareFunction (F : ℕ → ℓ²(ℤ, ℂ)) (hF : Summable (fun j : ℕ => ‖F j‖^2)) (x : ℤ) :
    squareMaximumValue F x ≤ squareFunctionValue F x := ciSup_le (fun j => squareFunctionValue_dominates F hF j x)

end PrimeSquares

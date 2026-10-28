import PrimeSquares.TemporalMaximumNorm
open scoped lp
namespace PrimeSquares
theorem finite_to_countable_maximum (F : ℕ → ℓ²(ℤ,ℂ)) {B : ℝ} (hB : 0 ≤ B)
    (hF : FiniteTemporalMajorants F B) :
    ∃ g : lp (fun _ : ℤ => ℝ) 2,(∀ x,0 ≤ g x) ∧
      (∀ j x,‖F j x‖ ≤ g x) ∧ ‖g‖ ≤ B := by
  have hb (x : ℤ) : BddAbove (Set.range (fun j : ℕ => ‖F j x‖)) :=
    ⟨B,by rintro _ ⟨j,rfl⟩;exact finiteTemporalMajorants_coordinate_bound F hF j x⟩
  refine ⟨temporalMaximumL2 F hB hF,?_,?_,temporalMaximumL2_norm F hB hF⟩
  · intro x
    exact (norm_nonneg (F 0 x)).trans (le_ciSup (hb x) 0)
  · intro j x
    exact le_ciSup (hb x) j
end PrimeSquares

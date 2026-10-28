import PrimeSquares.UnitMassMajorantLowerBound
open Finset MeasureTheory
open scoped lp
namespace PrimeSquares
theorem no_l2_unit_mass_majorant :
    ¬ ∃ g : lp (fun _ : ℤ => ℝ) 2,∀ j : ℕ,1 ≤ g (j : ℤ) := by
  rintro ⟨g,hg⟩
  obtain ⟨N,hN⟩ := exists_nat_gt (‖g‖^2)
  exact (not_le.mpr hN) (unitMass_majorant_square_lower g hg N)
end PrimeSquares

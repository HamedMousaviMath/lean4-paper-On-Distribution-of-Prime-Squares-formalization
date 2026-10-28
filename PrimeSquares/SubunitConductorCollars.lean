import PrimeSquares.ConductorCollarCenters
open Finset
namespace PrimeSquares
theorem conductorCollarCenters_eq_empty {Q : ℝ} {q₀ : ℕ}
    (hW : effectiveCollarCutoff Q q₀ < 1) : conductorCollarCenters Q q₀=∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro r hr
  have hd := (mem_conductorCollarCenters.mp hr).2.1
  have hz : ⌊effectiveCollarCutoff Q q₀⌋₊=0 := Nat.floor_eq_zero.mpr hW
  rw [hz] at hd
  exact (not_le_of_gt r.den_pos) hd
end PrimeSquares

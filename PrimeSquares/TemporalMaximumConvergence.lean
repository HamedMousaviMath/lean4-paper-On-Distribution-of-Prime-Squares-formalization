import PrimeSquares.InitialTemporalMaximumNorm
import Mathlib.Topology.Order.MonotoneConvergence
open scoped lp
namespace PrimeSquares
theorem initialTemporalMaximum_tendsto (F : ℕ → ℓ²(ℤ,ℂ)) {B : ℝ}
    (hF : FiniteTemporalMajorants F B) (x : ℤ) :
    Filter.Tendsto (fun n => initialTemporalMaximum F n x) Filter.atTop (nhds (⨆ j : ℕ,‖F j x‖)) := by
  have hb : BddAbove (Set.range (fun j : ℕ => ‖F j x‖)) :=
    ⟨B,by rintro _ ⟨j,rfl⟩;exact finiteTemporalMajorants_coordinate_bound F hF j x⟩
  have hc := tendsto_atTop_ciSup (partialSups_monotone (fun j : ℕ => ‖F j x‖))
    (bddAbove_range_partialSups.mpr hb)
  rw [ciSup_partialSups_eq hb] at hc
  exact hc
end PrimeSquares

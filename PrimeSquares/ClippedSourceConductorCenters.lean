import PrimeSquares.ChangingConductorCollarMaximum
open Finset
namespace PrimeSquares
theorem clipped_source_conductor_centers {Q R : ℝ} {q₀ : ℕ} (hQ : 0 < Q) (hq₀ : 0 < q₀) (hR : 0 ≤ R) :
    (((sourceRationalCenters R).filter (fun r => (r.den : ℝ) ≤ effectiveCollarCutoff Q q₀)).filter (fun r => q₀ ∣ r.den))=
      (conductorCollarCenters Q q₀).filter (fun r => (r.den : ℝ) ≤ R) := by
  ext r
  have hd : r.den ≤ ⌊effectiveCollarCutoff Q q₀⌋₊ ↔ (r.den : ℝ) ≤ effectiveCollarCutoff Q q₀ :=
    Nat.le_floor_iff (effectiveCollarCutoff_pos hQ hq₀).le
  simp only [mem_filter,mem_sourceRationalCenters hR,mem_conductorCollarCenters,hd]
  tauto
end PrimeSquares

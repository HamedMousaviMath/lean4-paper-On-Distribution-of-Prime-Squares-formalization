import PrimeSquares.CircleCollarSubsetExtension
open Finset
namespace PrimeSquares
theorem source_effective_conductor_filter {Q R : ℝ} {q₀ : ℕ} (hQ : 0 < Q) (hq₀ : 0 < q₀)
    (hR : effectiveCollarCutoff Q q₀ ≤ R) :
    ((sourceRationalCenters R).filter (fun r => (r.den : ℝ) ≤ effectiveCollarCutoff Q q₀)).filter
      (fun r => q₀ ∣ r.den)=conductorCollarCenters Q q₀ := by
  rw [sourceCenters_real_filter (effectiveCollarCutoff_pos hQ hq₀).le hR]
  rfl
end PrimeSquares

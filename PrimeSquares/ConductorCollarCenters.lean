import PrimeSquares.EffectiveCollarCutoff
open Finset
namespace PrimeSquares
noncomputable def conductorCollarCenters (Q : ℝ) (q₀ : ℕ) : Finset ℚ :=
  (canonicalRationalCenters ⌊effectiveCollarCutoff Q q₀⌋₊).filter (fun r => q₀ ∣ r.den)
theorem mem_conductorCollarCenters {Q : ℝ} {q₀ : ℕ} {r : ℚ} :
    r ∈ conductorCollarCenters Q q₀ ↔ r ∈ Set.Ico (0 : ℚ) 1 ∧
      r.den ≤ ⌊effectiveCollarCutoff Q q₀⌋₊ ∧ q₀ ∣ r.den := by
  simp only [conductorCollarCenters,mem_filter,mem_canonicalRationalCenters,and_assoc]
end PrimeSquares

import PrimeSquares.CanonicalRationalCenters
import Mathlib.Data.Nat.Log
open Finset
namespace PrimeSquares
noncomputable def sourceDyadicRationalCenters (s : ℕ) : Finset ℚ := by
  classical
  exact (canonicalRationalCenters (2^(s+1))).filter (fun r => Nat.log2 r.den=s)
theorem mem_sourceDyadicRationalCenters (s : ℕ) (r : ℚ) :
    r ∈ sourceDyadicRationalCenters s ↔ r ∈ Set.Ico (0 : ℚ) 1 ∧ Nat.log2 r.den=s := by
  classical
  simp only [sourceDyadicRationalCenters,mem_filter,mem_canonicalRationalCenters]
  constructor
  · exact fun h => ⟨h.1.1,h.2⟩
  · rintro ⟨hr,hs⟩
    have hb := (Nat.log2_eq_iff r.den_pos.ne').mp hs
    exact ⟨⟨hr,hb.2.le⟩,hs⟩
end PrimeSquares

import PrimeSquares.WrappedRationalArcGeometry
import Mathlib.Data.Rat.Floor

namespace PrimeSquares

theorem ratFract_canonical (r : ℚ) : Int.fract r ∈ Set.Ico (0 : ℚ) 1 :=
  ⟨Int.fract_nonneg r,Int.fract_lt_one r⟩

theorem rational_offset_canonical_lift (ξ : ℝ) (r : ℚ) :
    ξ-(r : ℝ) = ξ+((-⌊r⌋ : ℤ) : ℝ)-((Int.fract r : ℚ) : ℝ) := by
  simp only [Int.fract,Rat.cast_sub,Rat.cast_intCast,Int.cast_neg]
  ring

theorem ratFract_mem_sourceRationalCenters {R : ℝ} (hR : 0 ≤ R) (r : ℚ)
    (hd : (r.den : ℝ) ≤ R) : Int.fract r ∈ sourceRationalCenters R := by
  rw [mem_sourceRationalCenters hR]
  exact ⟨ratFract_canonical r,by simpa only [Rat.den_intFract] using hd⟩

end PrimeSquares

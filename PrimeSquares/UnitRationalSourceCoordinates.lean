import PrimeSquares.CanonicalUnitCardinality

namespace PrimeSquares

theorem unitRational_real (q : ℕ) (u : (ZMod q)ˣ) :
    ((unitRational q u : ℚ) : ℝ)=((u : ZMod q).val : ℝ)/(q : ℝ) := by
  simp only [unitRational,Rat.cast_div,Rat.cast_natCast]

theorem unitRational_numerator_mod (q : ℕ) [NeZero q] (u : (ZMod q)ˣ) :
    ((unitRational q u).num : ZMod q)=(u : ZMod q) := by
  rw [unitRational_num]
  simp only [Int.cast_natCast,ZMod.natCast_zmod_val]

end PrimeSquares

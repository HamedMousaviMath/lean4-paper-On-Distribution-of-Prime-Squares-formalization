import PrimeSquares.CanonicalRationalCenters

namespace PrimeSquares

noncomputable def unitRational (q : ℕ) (u : (ZMod q)ˣ) : ℚ :=
  ((u : ZMod q).val : ℚ)/(q : ℚ)

theorem unitRational_num (q : ℕ) [NeZero q] (u : (ZMod q)ˣ) :
    (unitRational q u).num=((u : ZMod q).val : ℤ) := by
  have hq : (0 : ℤ) < q := by exact_mod_cast NeZero.pos q
  have hc : Nat.Coprime (((u : ZMod q).val : ℤ).natAbs) ((q : ℤ).natAbs) := by
    simpa only [Int.natAbs_natCast] using ZMod.val_coe_unit_coprime u
  simpa only [unitRational,Int.cast_natCast] using Rat.num_div_eq_of_coprime hq hc

theorem unitRational_den (q : ℕ) [NeZero q] (u : (ZMod q)ˣ) :
    (unitRational q u).den=q := by
  have hq : (0 : ℤ) < q := by exact_mod_cast NeZero.pos q
  have hc : Nat.Coprime (((u : ZMod q).val : ℤ).natAbs) ((q : ℤ).natAbs) := by
    simpa only [Int.natAbs_natCast] using ZMod.val_coe_unit_coprime u
  have h : ((unitRational q u).den : ℤ)=(q : ℤ) := by
    simpa only [unitRational,Int.cast_natCast] using Rat.den_div_eq_of_coprime hq hc
  exact_mod_cast h

end PrimeSquares

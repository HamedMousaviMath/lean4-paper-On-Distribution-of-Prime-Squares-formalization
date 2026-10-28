import PrimeSquares.UnitRationalCanonical
import PrimeSquares.RationalNumeratorUnits

namespace PrimeSquares

theorem unitRational_numerator_recovery {M : ℕ} {r : ℚ}
    (hr : r ∈ canonicalRationalCenters M) :
    unitRational r.den (rationalNumeratorUnit r)=r := by
  rw [unitRational,rationalNumeratorUnit_val hr]
  have h := (canonicalRationalCenters_parameters hr).2.2.1
  have hc : (r.num.toNat : ℚ)=(r.num : ℚ) := by exact_mod_cast Int.toNat_of_nonneg h
  rw [hc,r.num_div_den]

theorem unitRational_injective (q : ℕ) [NeZero q] : Function.Injective (unitRational q) := by
  intro u v h
  have hn := congrArg Rat.num h
  rw [unitRational_num,unitRational_num] at hn
  have hv : (u : ZMod q).val=(v : ZMod q).val := by exact_mod_cast hn
  apply Units.ext
  exact ZMod.val_injective q hv

end PrimeSquares

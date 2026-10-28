import PrimeSquares.UnitSquareShift

/-!
# Character scaling and unit invariance

The standard additive character at modulus m*d restricted to multiples of d
is the standard character at modulus m. Both coordinate orders are proved
from the complex exponential definition. These identities avoid assuming an
incorrect unscaled factorization of the standard character under CRT.
-/

open Finset

namespace PrimeSquares

theorem stdAddChar_mul_modulus (m d : ℕ) [NeZero m] [NeZero d] (k : ℤ) :
    ZMod.stdAddChar (((d : ℤ) * k : ℤ) : ZMod (m * d)) =
      ZMod.stdAddChar (k : ZMod m) := by
  rw [ZMod.stdAddChar_coe, ZMod.stdAddChar_coe]
  congr 1
  push_cast
  have hm : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  field_simp

theorem stdAddChar_scale (m d : ℕ) [NeZero m] [NeZero d] (x : ZMod (m * d)) :
    ZMod.stdAddChar ((d : ZMod (m * d)) * x) =
      ZMod.stdAddChar (ZMod.castHom (Nat.dvd_mul_right m d) (ZMod m) x) := by
  obtain ⟨k, rfl⟩ := ZMod.intCast_surjective x
  simpa only [Int.cast_mul, Int.cast_natCast, map_intCast] using
    stdAddChar_mul_modulus m d k

theorem stdAddChar_scale_left (m d : ℕ) [NeZero m] [NeZero d] (x : ZMod (m * d)) :
    ZMod.stdAddChar ((m : ZMod (m * d)) * x) =
      ZMod.stdAddChar (ZMod.castHom (Nat.dvd_mul_left d m) (ZMod d) x) := by
  obtain ⟨k, rfl⟩ := ZMod.intCast_surjective x
  rw [map_intCast]
  have hcast : (m : ZMod (m * d)) * (k : ZMod (m * d)) =
      (((m : ℤ) * k : ℤ) : ZMod (m * d)) := by push_cast; rfl
  rw [hcast, ZMod.stdAddChar_coe, ZMod.stdAddChar_coe]
  congr 1
  push_cast
  have hm : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  field_simp

theorem ramanujanSum_mul_unit (q : ℕ) [NeZero q] (m : ZMod q) (u : (ZMod q)ˣ) :
    ramanujanSum q (m * u) = ramanujanSum q m := by
  unfold ramanujanSum
  rw [sum_unit_filter_eq_sum_units, sum_unit_filter_eq_sum_units]
  exact Fintype.sum_equiv (Equiv.mulLeft u)
    (fun a : (ZMod q)ˣ => ZMod.stdAddChar ((m * (u : ZMod q)) * (a : ZMod q)))
    (fun a : (ZMod q)ˣ => ZMod.stdAddChar (m * (a : ZMod q)))
    (fun a => by simp [mul_assoc])

end PrimeSquares

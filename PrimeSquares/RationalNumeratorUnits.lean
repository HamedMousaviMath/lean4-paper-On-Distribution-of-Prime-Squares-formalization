import PrimeSquares.CanonicalRationalCenters
import PrimeSquares.CircleRationalModelNorm

namespace PrimeSquares

noncomputable def rationalNumeratorUnit (r : ℚ) : (ZMod r.den)ˣ :=
  ((ZMod.coe_int_isUnit_iff_isCoprime r.num r.den).mpr r.isCoprime_num_den.symm).unit

theorem rationalNumeratorUnit_coe (r : ℚ) :
    (rationalNumeratorUnit r : ZMod r.den)=(r.num : ZMod r.den) := by
  simp only [rationalNumeratorUnit,IsUnit.unit_spec]

theorem rationalNumeratorUnit_val {M : ℕ} {r : ℚ}
    (hr : r ∈ canonicalRationalCenters M) :
    (rationalNumeratorUnit r : ZMod r.den).val=r.num.toNat := by
  have h := canonicalRationalCenters_parameters hr
  have hn : (r.num.toNat : ℤ)=r.num := Int.toNat_of_nonneg h.2.2.1
  have he : (r.num : ZMod r.den)=(r.num.toNat : ZMod r.den) := by
    simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z : ZMod r.den)) hn.symm
  have : NeZero r.den := ⟨r.den_pos.ne'⟩
  rw [rationalNumeratorUnit_coe,he,ZMod.val_natCast_of_lt (by omega : r.num.toNat < r.den)]

end PrimeSquares

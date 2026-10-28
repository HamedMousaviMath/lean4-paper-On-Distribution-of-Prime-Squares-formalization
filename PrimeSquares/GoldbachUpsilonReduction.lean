import PrimeSquares.GoldbachPrimitiveProgression

set_option autoImplicit false
open Finset
namespace PrimeSquares

instance goldbachLCMNeZero (m n : ℕ) [NeZero m] [NeZero n] : NeZero (m.lcm n) :=
  ⟨(Nat.lcm_pos (NeZero.pos m) (NeZero.pos n)).ne'⟩

noncomputable def goldbachZModFinEquiv (m : ℕ) [NeZero m] : ZMod m≃Fin m where
  toFun r := ⟨r.val,r.val_lt⟩
  invFun r := r.val
  left_inv r := ZMod.natCast_zmod_val r
  right_inv r := Fin.ext (ZMod.val_natCast_of_lt r.isLt)

theorem goldbach_sum_units_range (m : ℕ) [NeZero m] (f : ℕ→ℂ) :
    (∑ u : (ZMod m)ˣ,f (u:ZMod m).val)=
      ∑ r∈range m,if r.Coprime m then f r else 0 := by
  classical
  rw [←sum_unit_filter_eq_sum_units m (fun r => f r.val)]
  have he : (∑ r : ZMod m,if IsUnit r then f r.val else 0)=
      ∑ r : Fin m,if r.val.Coprime m then f r.val else 0 := by
    apply Fintype.sum_equiv (goldbachZModFinEquiv m)
    intro r
    have hu : IsUnit r↔r.val.Coprime m := by
      simpa only [ZMod.natCast_zmod_val] using ZMod.isUnit_iff_coprime r.val m
    simp only [hu,goldbachZModFinEquiv,Equiv.coe_fn_mk]
    rfl
  rw [he]
  exact Fin.sum_univ_eq_sum_range (fun r => if r.Coprime m then f r else 0) m

theorem goldbach_unit_lcm_residue_sum (k q a : ℕ) [NeZero k] [NeZero q]
    (f : ZMod q→ℂ) :
    (∑ u : (ZMod (k.lcm q))ˣ,
      if ZMod.castHom (Nat.dvd_lcm_left k q) (ZMod k) (u:ZMod (k.lcm q))=(a:ZMod k)
      then f (ZMod.castHom (Nat.dvd_lcm_right k q) (ZMod q) (u:ZMod (k.lcm q))) else 0)=
      ∑ r∈goldbachMajorResidues k q a,f (r:ZMod q) := by
  classical
  have he (u : (ZMod (k.lcm q))ˣ) :
      (if ZMod.castHom (Nat.dvd_lcm_left k q) (ZMod k) (u:ZMod (k.lcm q))=(a:ZMod k)
      then f (ZMod.castHom (Nat.dvd_lcm_right k q) (ZMod q) (u:ZMod (k.lcm q))) else 0)=
      if (u:ZMod (k.lcm q)).val%k=a%k then f ((u:ZMod (k.lcm q)).val:ZMod q) else 0 := by
    rw [←goldbach_reduction_val (Nat.dvd_lcm_left k q),←goldbach_reduction_val (Nat.dvd_lcm_right k q)]
    simp only [ZMod.natCast_eq_natCast_iff]
    rfl
  simp_rw [he]
  rw [goldbach_sum_units_range (k.lcm q) (fun r : ℕ => if r%k=a%k then f (r:ZMod q) else 0)]
  simp only [goldbachMajorResidues,sum_filter]
  apply sum_congr rfl
  intro r _
  by_cases hc : r.Coprime (k.lcm q) <;> by_cases hr : r%k=a%k <;> simp [hc,hr]

theorem goldbach_upsilon_lcm_unit_average (k q a : ℕ) [NeZero k] [NeZero q]
    (ha : a.Coprime k) (α : ZMod q) :
    upsilon q k (a:ℤ) α=(k.totient:ℂ)*
      (((k.lcm q).totient:ℂ)⁻¹*(∑ u : (ZMod (k.lcm q))ˣ,
        if ZMod.castHom (Nat.dvd_lcm_left k q) (ZMod k) (u:ZMod (k.lcm q))=(a:ZMod k)
        then ZMod.stdAddChar ((-α)*ZMod.castHom (Nat.dvd_lcm_right k q) (ZMod q) (u:ZMod (k.lcm q))) else 0)) := by
  rw [goldbach_unit_lcm_residue_sum k q a (fun r : ZMod q => ZMod.stdAddChar ((-α)*r))]
  have he := goldbach_major_upsilon_identity k q a ha (-α)
  simp only [neg_neg] at he
  rw [he]
  have hk : (k.totient:ℂ)≠0 := by exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos k)).ne'
  field_simp

theorem goldbach_unit_reduction_comp (a b c : ℕ) [NeZero c] (hab : a∣b) (hbc : b∣c)
    (u : (ZMod c)ˣ) :
    ZMod.castHom hab (ZMod a) (ZMod.unitsMap hbc u:ZMod b)=
      ZMod.castHom (hab.trans hbc) (ZMod a) (u:ZMod c) := by
  change ZMod.castHom hab (ZMod a) (ZMod.castHom hbc (ZMod b) (u:ZMod c))=_
  rw [←RingHom.comp_apply,ZMod.castHom_comp]

theorem goldbach_upsilon_frequency_reduction (q d k a : ℕ) [NeZero q] [NeZero d] [NeZero k]
    (ha : a.Coprime k) (β : ℤ) :
    upsilon (q*d) k (a:ℤ) (((d:ℤ)*β:ℤ):ZMod (q*d))=upsilon q k (a:ℤ) (β:ZMod q) := by
  classical
  let L := k.lcm (q*d)
  let L₀ := k.lcm q
  have hd : L₀∣L := Nat.lcm_dvd (Nat.dvd_lcm_left k (q*d))
    ((Nat.dvd_mul_right q d).trans (Nat.dvd_lcm_right k (q*d)))
  let f (u : (ZMod L₀)ˣ) : ℂ :=
    if ZMod.castHom (Nat.dvd_lcm_left k q) (ZMod k) (u:ZMod L₀)=(a:ZMod k)
    then ZMod.stdAddChar ((-(β:ZMod q))*ZMod.castHom (Nat.dvd_lcm_right k q) (ZMod q) (u:ZMod L₀)) else 0
  have he (u : (ZMod L)ˣ) :
      (if ZMod.castHom (Nat.dvd_lcm_left k (q*d)) (ZMod k) (u:ZMod L)=(a:ZMod k)
      then ZMod.stdAddChar ((-(((d:ℤ)*β:ℤ):ZMod (q*d)))*
        ZMod.castHom (Nat.dvd_lcm_right k (q*d)) (ZMod (q*d)) (u:ZMod L)) else 0)=f (ZMod.unitsMap hd u) := by
    dsimp only [f]
    rw [goldbach_unit_reduction_comp,goldbach_unit_reduction_comp]
    split_ifs
    · have hp : -(((d:ℤ)*β:ℤ):ZMod (q*d))*
          ZMod.castHom (Nat.dvd_lcm_right k (q*d)) (ZMod (q*d)) (u:ZMod L)=
          (d:ZMod (q*d))*((-(β:ZMod (q*d)))*
          ZMod.castHom (Nat.dvd_lcm_right k (q*d)) (ZMod (q*d)) (u:ZMod L)) := by push_cast;ring
      rw [hp,stdAddChar_scale q d]
      simp only [map_mul,map_neg,map_intCast]
      rw [←RingHom.comp_apply,ZMod.castHom_comp]
    · rfl
  rw [goldbach_upsilon_lcm_unit_average k (q*d) a ha,goldbach_upsilon_lcm_unit_average k q a ha]
  congr 1
  simp_rw [he]
  exact goldbach_normalized_units_sum_pullback L L₀ hd f

end PrimeSquares

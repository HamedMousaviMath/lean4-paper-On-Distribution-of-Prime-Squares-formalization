import PrimeSquares.GeneralLocalEuler
import PrimeSquares.GoldbachFiniteUnitAverages

set_option autoImplicit false
open Finset
namespace PrimeSquares

theorem goldbach_modular_multiplier_constant (q g ℓ : ℕ) [NeZero q]
    (hg : g∣q) (hℓ : q∣ℓ*g) (b : ℤ) (v : ZMod q)
    (hv : ZMod.castHom hg (ZMod g) v=(b:ZMod g)) :
    (ℓ:ZMod q)*v=(ℓ:ZMod q)*(b:ZMod q) := by
  obtain ⟨z,rfl⟩ := ZMod.intCast_surjective v
  rw [map_intCast] at hv
  have hd : (g:ℤ)∣z-b := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd (z-b) g).mp
    simpa only [Int.cast_sub,sub_eq_zero] using hv
  have hd' : (q:ℤ)∣(ℓ:ℤ)*(z-b) := by
    have hh : (q:ℤ)∣(ℓ:ℤ)*(g:ℤ) := by exact_mod_cast hℓ
    exact hh.trans (mul_dvd_mul_left (ℓ:ℤ) hd)
  have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd ((ℓ:ℤ)*(z-b)) q).mpr hd'
  simpa only [Int.cast_mul,Int.cast_sub,Int.cast_natCast,mul_sub,sub_eq_zero] using hz

theorem goldbach_general_coefficient_conductor (q k ℓ : ℕ) [NeZero q] [NeZero k]
    (hq : q∣ℓ*k) (b n : ℤ) (hb : IsCoprime (k:ℤ) b) :
    generalCoefficient q k (ℓ:ℤ) b n=cohenCorrelation q (n-(ℓ:ℤ)*b)/(q.totient:ℂ) := by
  classical
  let g := q.gcd k
  have hg : g∣q := Nat.gcd_dvd_left q k
  have hbu : IsUnit (b:ZMod g) := (ZMod.coe_int_isUnit_iff_isCoprime b g).mpr
    (integer_coprime_of_nat_dvd g k b hb (Nat.gcd_dvd_right q k))
  have hℓ : q∣ℓ*g := by
    have ht : q∣q.gcd ℓ*q.gcd k := Nat.dvd_gcd_mul_gcd_iff_dvd_mul.mpr hq
    exact ht.trans (Nat.mul_dvd_mul (Nat.gcd_dvd_right q ℓ) (dvd_refl g))
  have hterm (v : (ZMod q)ˣ)
      (hv : ZMod.castHom hg (ZMod g) (v:ZMod q)=(b:ZMod g)) :
      quadraticRamanujanSum q ((n:ZMod q)-((ℓ:ℤ):ZMod q)*(v:ZMod q))=
        cohenCorrelation q (n-(ℓ:ℤ)*b) := by
    rw [Int.cast_natCast,goldbach_modular_multiplier_constant q g ℓ hg hℓ b _ hv,
      cohenCorrelation_eq,Int.cast_sub,Int.cast_mul,Int.cast_natCast]
  let f (u : (ZMod g)ˣ) : ℂ := if u=hbu.unit then 1 else 0
  have he (v : (ZMod q)ˣ) :
      f (ZMod.unitsMap hg v)=
        if ZMod.castHom hg (ZMod g) (v:ZMod q)=(b:ZMod g) then 1 else 0 := by
    dsimp only [f]
    have hh : ZMod.unitsMap hg v=hbu.unit ↔
        ZMod.castHom hg (ZMod g) (v:ZMod q)=(b:ZMod g) := by
      constructor
      · intro hv
        exact (congrArg (fun u : (ZMod g)ˣ=>(u:ZMod g)) hv).trans hbu.unit_spec
      · intro hv
        exact Units.ext (hv.trans hbu.unit_spec.symm)
    simp only [hh]
  have hm := goldbach_normalized_units_sum_pullback q g hg f
  simp only [he,f,sum_ite_eq',mem_univ,ite_true,mul_one] at hm
  rw [generalCoefficient_as_quadratic]
  have hs : (∑ v : (ZMod q)ˣ,
      if ZMod.castHom hg (ZMod g) (v:ZMod q)=(b:ZMod g)
      then quadraticRamanujanSum q ((n:ZMod q)-((ℓ:ℤ):ZMod q)*(v:ZMod q)) else 0)=
      (∑ v : (ZMod q)ˣ,if ZMod.castHom hg (ZMod g) (v:ZMod q)=(b:ZMod g) then (1:ℂ) else 0)*
        cohenCorrelation q (n-(ℓ:ℤ)*b) := by
    rw [sum_mul]
    apply sum_congr rfl
    intro v _
    split_ifs with hv
    · rw [hterm v hv,one_mul]
    · rw [zero_mul]
  rw [hs]
  have hqφ : (q.totient:ℂ)≠0 := by exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  have hgφ : (g.totient:ℂ)≠0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.gcd_pos_of_pos_left k (NeZero.pos q))).ne'
  change (g.totient:ℂ)/(q.totient:ℂ)^2*(_*_)=_
  have hm' : (∑ v : (ZMod q)ˣ,if ZMod.castHom hg (ZMod g) (v:ZMod q)=(b:ZMod g) then (1:ℂ) else 0)=
      (q.totient:ℂ)/(g.totient:ℂ) := by
    apply (mul_left_cancel₀ (inv_ne_zero hqφ))
    rw [hm]
    field_simp
  rw [hm']
  field_simp

end PrimeSquares

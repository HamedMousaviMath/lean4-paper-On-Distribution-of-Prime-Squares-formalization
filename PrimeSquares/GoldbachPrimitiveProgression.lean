import PrimeSquares.GoldbachFiniteUnitAverages

set_option autoImplicit false
open Finset
namespace PrimeSquares

theorem goldbach_progression_exponential_zero_translation (q g : ℕ) [NeZero q]
    (hg : g∣q) (b : ZMod g) (a t : ZMod q) (ha : IsUnit a)
    (ht : t^2=0) (hnt : t≠0) (hgt : ZMod.castHom hg (ZMod g) t=0) :
    progressionExponentialSum q g hg b a=0 := by
  classical
  let ρ := ZMod.castHom hg (ZMod g)
  let f (u : (ZMod q)ˣ) : ℂ := if ρ (u:ZMod q)=b then ZMod.stdAddChar (-(a*(u:ZMod q))) else 0
  have hphase : ZMod.stdAddChar (-(a*t))≠(1:ℂ) := by
    intro hh
    have hz : -(a*t)=0 := ZMod.injective_stdAddChar (hh.trans (AddChar.map_zero_eq_one _).symm)
    exact hnt (ha.mul_right_eq_zero.mp (neg_eq_zero.mp hz))
  have hs : (∑ u,f u)=ZMod.stdAddChar (-(a*t))*(∑ u,f u) := by
    calc
      _=∑ u : (ZMod q)ˣ,f (nilpotentAddEquiv t ht u) := (Equiv.sum_comp (nilpotentAddEquiv t ht) f).symm
      _=∑ u : (ZMod q)ˣ,ZMod.stdAddChar (-(a*t))*f u := by
        apply sum_congr rfl
        intro u _
        change (if ρ ((u:ZMod q)+t)=b then ZMod.stdAddChar (-(a*((u:ZMod q)+t))) else 0)=_
        rw [map_add,hgt,add_zero]
        dsimp only [f]
        split_ifs
        · rw [←AddChar.map_add_eq_mul]
          congr 1
          ring
        · rw [mul_zero]
      _=_ := (mul_sum _ _ _).symm
  have hz : (ZMod.stdAddChar (-(a*t))-1)*(∑ u,f u)=0 := by
    rw [sub_mul,one_mul,←hs,sub_self]
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hphase)

theorem goldbach_progression_exponential_noncoprime (g h : ℕ) [NeZero g] [NeZero h]
    (hc : ¬g.Coprime h) (b : ZMod g) (a : ZMod (g*h)) (ha : IsUnit a) :
    progressionExponentialSum (g*h) g (Nat.dvd_mul_right g h) b a=0 := by
  obtain ⟨p,hp,hpg,hph⟩ := Nat.Prime.not_coprime_iff_dvd.mp hc
  obtain ⟨l,hl⟩ := hpg
  obtain ⟨k,hk⟩ := hph
  have hkpos : 0<k := by
    by_contra! hz
    have hh : h=0 := by rw [hk,show k=0 by omega,mul_zero]
    exact NeZero.ne h hh
  let t : ZMod (g*h) := (g*k:ℕ)
  have ht : t^2=0 := by
    dsimp only [t]
    rw [←Nat.cast_pow,ZMod.natCast_eq_zero_iff]
    refine ⟨l*k,?_⟩
    rw [hl,hk]
    ring
  have hnt : t≠0 := by
    intro hz
    have hd : g*h∣g*k := (ZMod.natCast_eq_zero_iff (g*k) (g*h)).mp hz
    apply Nat.not_dvd_of_pos_of_lt (Nat.mul_pos (NeZero.pos g) hkpos)
    calc
      g*k<(g*k)*p := by simpa only [mul_one] using Nat.mul_lt_mul_of_pos_left hp.one_lt (Nat.mul_pos (NeZero.pos g) hkpos)
      _=g*h := by rw [hk];ring
    exact hd
  have hgt : ZMod.castHom (Nat.dvd_mul_right g h) (ZMod g) t=0 := by
    change ZMod.castHom (Nat.dvd_mul_right g h) (ZMod g) ((g*k:ℕ):ZMod (g*h))=0
    rw [map_natCast,Nat.cast_mul,ZMod.natCast_self,zero_mul]
  exact goldbach_progression_exponential_zero_translation _ _ _ b a t ha ht hnt hgt

theorem goldbach_progression_exponential_coprime_norm (g h : ℕ) [NeZero g] [NeZero h]
    (hc : g.Coprime h) (b : (ZMod g)ˣ) (a : ZMod (g*h)) (ha : IsUnit a) :
    ‖progressionExponentialSum (g*h) g (Nat.dvd_mul_right g h) b a‖≤1 := by
  classical
  let un : (ZMod g)ˣ := ZMod.unitOfCoprime h hc.symm
  let um : (ZMod h)ˣ := ZMod.unitOfCoprime g hc
  let E : (ZMod g)ˣ×(ZMod h)ˣ ≃ (ZMod (g*h))ˣ :=
    (Equiv.prodCongr (Equiv.mulLeft un) (Equiv.mulLeft um)).trans (crtUnitsEquiv hc).symm.toEquiv
  let ag : ZMod g := ZMod.castHom (Nat.dvd_mul_right g h) (ZMod g) (-a)
  let ah : ZMod h := ZMod.castHom (Nat.dvd_mul_left h g) (ZMod h) (-a)
  have huh : IsUnit ah := ha.neg.map (ZMod.castHom (Nat.dvd_mul_left h g) (ZMod h))
  have hs : progressionExponentialSum (g*h) g (Nat.dvd_mul_right g h) b a=
      ZMod.stdAddChar (ag*((un⁻¹*b:(ZMod g)ˣ):ZMod g))*ramanujanSum h ah := by
    unfold progressionExponentialSum
    calc
      _=∑ uv : (ZMod g)ˣ×(ZMod h)ˣ,
          if ZMod.castHom (Nat.dvd_mul_right g h) (ZMod g) (E uv:ZMod (g*h))=(b:ZMod g)
          then ZMod.stdAddChar (-(a*(E uv:ZMod (g*h)))) else 0 := (Equiv.sum_comp E _).symm
      _=∑ uv : (ZMod g)ˣ×(ZMod h)ˣ,if uv.1=un⁻¹*b
          then ZMod.stdAddChar (ag*(uv.1:ZMod g))*ZMod.stdAddChar (ah*(uv.2:ZMod h)) else 0 := by
        apply sum_congr rfl
        intro uv _
        have he := crtUnitsEquiv_cast hc ((crtUnitsEquiv hc).symm (un*uv.1,um*uv.2))
        simp only [MulEquiv.apply_symm_apply] at he
        have hcond : ZMod.castHom (Nat.dvd_mul_right g h) (ZMod g) (E uv:ZMod (g*h))=(b:ZMod g) ↔
            uv.1=un⁻¹*b := by
          change ZMod.castHom (Nat.dvd_mul_right g h) (ZMod g)
            (((crtUnitsEquiv hc).symm (un*uv.1,um*uv.2):(ZMod (g*h))ˣ):ZMod (g*h))=(b:ZMod g) ↔ _
          rw [←he.1,Units.val_inj]
          exact ⟨fun hh => by rw [←hh];group,fun hh => by rw [hh];group⟩
        simp only [hcond]
        split_ifs
        · have hp := crtUnitsEquiv_scaled_phase hc uv.1 uv.2 (-a)
          change ZMod.stdAddChar (-(a*(((crtUnitsEquiv hc).symm (un*uv.1,um*uv.2):(ZMod (g*h))ˣ):ZMod (g*h))))=_
          simpa only [un,um,ag,ah,neg_mul] using hp
        · rfl
      _=_ := by
        rw [Fintype.sum_prod_type]
        simp only [sum_ite_irrel,sum_const_zero,sum_ite_eq',mem_univ,ite_true]
        rw [ramanujanSum,sum_unit_filter_eq_sum_units,mul_sum]
  rw [hs,norm_mul,norm_stdAddChar,one_mul,←huh.unit_spec,ramanujanSum_unit_eq_moebius,Complex.norm_intCast]
  exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n:=h))

end PrimeSquares

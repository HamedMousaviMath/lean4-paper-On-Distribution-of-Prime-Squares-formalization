import PrimeSquares.GoldbachMajorLCMReindexing

set_option autoImplicit false
namespace PrimeSquares

theorem goldbach_coprime_of_congruence {a b m : ℕ} (h : Nat.ModEq m a b)
    (hb : b.Coprime m) : a.Coprime m := by
  rw [Nat.coprime_iff_gcd_eq_one,h.gcd_eq]
  exact hb.gcd_eq_one

theorem goldbach_modular_linear_residue (n a b : ℕ) (hn : 0<n) (ha : a.Coprime n) :
    ∃ r : ℕ,r<n ∧ Nat.ModEq n (a*r) b := by
  let inst : NeZero n := ⟨hn.ne'⟩
  let u := ZMod.unitOfCoprime a ha
  let z : ZMod n := (↑u⁻¹:ZMod n)*(b:ZMod n)
  refine ⟨z.val,ZMod.val_lt z,?_⟩
  apply (ZMod.natCast_eq_natCast_iff (a*z.val) b n).mp
  rw [Nat.cast_mul,ZMod.natCast_zmod_val,←ZMod.coe_unitOfCoprime a ha]
  change (↑u:ZMod n)*((↑u⁻¹:ZMod n)*(b:ZMod n))=(b:ZMod n)
  rw [←mul_assoc,Units.mul_inv,one_mul]

theorem goldbach_lower_sieve_residue (d : ℕ) (hd : 0<d) (hd6 : d.Coprime 6) :
    ∃ a : ℕ,a<24*d ∧ Nat.ModEq 24 a 11 ∧ Nat.ModEq d a 1 ∧ a.Coprime (24*d) := by
  have h2 : (2:ℕ).Coprime d := Nat.Coprime.of_dvd_left (by decide : 2∣6) hd6.symm
  have h24 : (24:ℕ).Coprime d := by
    rw [show (24:ℕ)=2^2*6 by decide]
    exact (h2.pow_left 2).mul_left hd6.symm
  let a := Nat.chineseRemainder h24 11 1
  have hA := a.prop
  refine ⟨a.val,Nat.chineseRemainder_lt_mul h24 11 1 (by decide) hd.ne',hA.1,hA.2,?_⟩
  exact (goldbach_coprime_of_congruence hA.1 (by decide : Nat.Coprime 11 24)).mul_right
    (goldbach_coprime_of_congruence hA.2 (by simp))

theorem goldbach_lower_sieve_residue_from_support (d : ℕ)
    (hsupport : ∀ p : ℕ,p.Prime → p∣d → 3<p) :
    ∃ a : ℕ,a<24*d ∧ Nat.ModEq 24 a 11 ∧ Nat.ModEq d a 1 ∧ a.Coprime (24*d) := by
  have hd : 0<d := by
    by_contra h
    have hd0 : d=0 := by omega
    have hh := hsupport 2 (by decide) (by rw [hd0]; exact dvd_zero 2)
    omega
  have hd6 : d.Coprime 6 := by
    apply Nat.coprime_of_dvd
    intro p hp hpd hp6
    have hlarge := hsupport p hp hpd
    have hpm : p∣2*3 := hp6
    rcases hp.dvd_mul.mp hpm with hp2|hp3
    · have he := (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 2)).mp hp2
      omega
    · have he := (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 3)).mp hp3
      omega
  exact goldbach_lower_sieve_residue d hd hd6

theorem goldbach_upper_sieve_residue (v d : ℕ) (hv : v.Coprime 6) (hd : 0<d)
    (hdℓ : d.Coprime (12*(2*v))) :
    ∃ a : ℕ,a<12*d ∧ Nat.ModEq 12 (v*a) 5 ∧
      Nat.ModEq d ((2*v)*a+1) 0 ∧ a.Coprime (12*d) := by
  have hv2 : v.Coprime 2 := Nat.Coprime.of_dvd_right (by decide : 2∣6) hv
  have hv12 : v.Coprime 12 := by
    rw [show (12:ℕ)=2*6 by decide]
    exact hv2.mul_right hv
  have hd12 : d.Coprime 12 := Nat.Coprime.of_dvd_right (dvd_mul_right 12 (2*v)) hdℓ
  have hℓd : (2*v).Coprime d :=
    (Nat.Coprime.of_dvd_right (dvd_mul_left (2*v) 12) hdℓ).symm
  obtain ⟨r₀,_,hr₀⟩ := goldbach_modular_linear_residue 12 v 5 (by decide) hv12
  obtain ⟨r₁,_,hr₁⟩ := goldbach_modular_linear_residue d (2*v) (d-1) hd hℓd
  have hpred : (d-1).Coprime d := by
    have hh : (d-1).Coprime ((d-1)+1) := by simp [Nat.coprime_iff_gcd_eq_one]
    simpa only [Nat.sub_add_cancel (show 1≤d by omega)] using hh
  have hr₀cop : r₀.Coprime 12 := (Nat.coprime_mul_iff_left.mp
    (goldbach_coprime_of_congruence hr₀ (by decide : Nat.Coprime 5 12))).2
  have hr₁cop : r₁.Coprime d := (Nat.coprime_mul_iff_left.mp
    (goldbach_coprime_of_congruence hr₁ hpred)).2
  let a := Nat.chineseRemainder hd12.symm r₀ r₁
  have hA := a.prop
  have hva : Nat.ModEq 12 (v*a.val) 5 := (hA.1.mul_left v).trans hr₀
  have hda : Nat.ModEq d ((2*v)*a.val+1) 0 := by
    have hh := ((hA.2.mul_left (2*v)).trans hr₁).add_right 1
    have hz : Nat.ModEq d d 0 := Nat.modEq_zero_iff_dvd.mpr (dvd_refl d)
    have hh' : Nat.ModEq d ((2*v)*a.val+1) d := by
      simpa only [Nat.sub_add_cancel (show 1≤d by omega)] using hh
    exact hh'.trans hz
  exact ⟨a.val,Nat.chineseRemainder_lt_mul hd12.symm r₀ r₁ (by decide) hd.ne',hva,hda,
    (goldbach_coprime_of_congruence hA.1 hr₀cop).mul_right
      (goldbach_coprime_of_congruence hA.2 hr₁cop)⟩

theorem goldbach_upper_sieve_common_product_residue (d : ℕ) (hd : 0<d)
    (hd12 : d.Coprime 12) :
    ∃ b : ℕ,b<12*d ∧ b.gcd (12*d)=2 ∧ Nat.ModEq 12 b 10 ∧ Nat.ModEq d (b+1) 0 ∧
      ∀ v a : ℕ,Nat.ModEq 12 (v*a) 5 → Nat.ModEq d ((2*v)*a+1) 0 →
        Nat.ModEq (12*d) ((2*v)*a) b := by
  let b := Nat.chineseRemainder hd12.symm 10 (d-1)
  have hB := b.prop
  have hpred : (d-1).Coprime d := by
    have hh : (d-1).Coprime ((d-1)+1) := by simp [Nat.coprime_iff_gcd_eq_one]
    simpa only [Nat.sub_add_cancel (show 1≤d by omega)] using hh
  have hbD := goldbach_coprime_of_congruence hB.2 hpred
  have hbplus : Nat.ModEq d (b.val+1) 0 := by
    have hh := hB.2.add_right 1
    have hz : Nat.ModEq d d 0 := Nat.modEq_zero_iff_dvd.mpr (dvd_refl d)
    have hh' : Nat.ModEq d (b.val+1) d := by
      simpa only [Nat.sub_add_cancel (show 1≤d by omega)] using hh
    exact hh'.trans hz
  have hbgcd : b.val.gcd (12*d)=2 := by
    rw [Nat.gcd_comm,(hbD.symm.gcd_mul_right_cancel 12),←Nat.gcd_comm b.val 12,hB.1.gcd_eq]
    decide
  refine ⟨b.val,Nat.chineseRemainder_lt_mul hd12.symm 10 (d-1) (by decide) hd.ne',
    hbgcd,hB.1,hbplus,?_⟩
  intro v a hva hda
  have h12 : Nat.ModEq 12 ((2*v)*a) b.val := by
    have hh := hva.mul_left 2
    have hh' : Nat.ModEq 12 ((2*v)*a) 10 := by
      simpa only [mul_assoc,show 2*5=10 by decide] using hh
    exact hh'.trans hB.1.symm
  have hD : Nat.ModEq d ((2*v)*a) b.val :=
    (hda.trans hbplus.symm).add_right_cancel' 1
  simpa only [hd12.symm.lcm_eq_mul] using Nat.mod_lcm h12 hD

end PrimeSquares

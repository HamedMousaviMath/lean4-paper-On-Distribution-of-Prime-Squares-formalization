import PrimeSquares.GoldbachArithmeticHarmonic

set_option autoImplicit false
open Finset
open scoped ArithmeticFunction.Moebius
namespace PrimeSquares

theorem goldbach_general_coefficient_of_dvd (q k : ℕ) [NeZero q] [NeZero k]
    (hqk : q∣k) (ℓ b n : ℤ) (hb : IsUnit (b:ZMod q)) :
    generalCoefficient q k ℓ b n=cohenCorrelation q (n-ℓ*b)/(q.totient:ℂ) := by
  classical
  rw [generalCoefficient_as_quadratic]
  simp_rw [unit_reduction_eq_iff q k hqk b hb]
  rw [sum_ite_eq',ite_eq_left (mem_univ _),hb.unit_spec]
  rw [Nat.gcd_eq_left_iff_dvd.mpr hqk,cohenCorrelation_eq,Int.cast_sub,Int.cast_mul]
  have hφ : (q.totient:ℂ)≠0 := by exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  field_simp

theorem goldbach_general_coefficient_of_coprime_unit (q k : ℕ) [NeZero q] [NeZero k]
    (hqk : q.Coprime k) (ℓ b n : ℤ) (hℓ : IsUnit (ℓ:ZMod q)) :
    generalCoefficient q k ℓ b n=(μ q:ℂ)*cohenCorrelation q n/(q.totient:ℂ)^2 := by
  classical
  have : Subsingleton (ZMod (q.gcd k)) := by rw [hqk.gcd_eq_one];infer_instance
  have hP (v : (ZMod q)ˣ) :
      ZMod.castHom (Nat.gcd_dvd_left q k) (ZMod (q.gcd k)) (v:ZMod q)=(b:ZMod (q.gcd k)) :=
    Subsingleton.elim _ _
  rw [generalCoefficient_as_quadratic]
  simp_rw [ite_eq_left (hP _)]
  have hs : (∑ v : (ZMod q)ˣ,quadraticRamanujanSum q ((n:ZMod q)-(ℓ:ZMod q)*(v:ZMod q)))=
      ∑ v : (ZMod q)ˣ,quadraticRamanujanSum q ((n:ZMod q)-(v:ZMod q)) := by
    have he := Equiv.sum_comp (Equiv.mulLeft hℓ.unit)
      (fun v : (ZMod q)ˣ => quadraticRamanujanSum q ((n:ZMod q)-(v:ZMod q)))
    simpa only [Equiv.coe_mulLeft,Units.val_mul,hℓ.unit_spec] using he
  rw [hs,linear_quadratic_cohen_identity,hqk.gcd_eq_one,Nat.totient_one,Nat.cast_one,cohenCorrelation_eq]
  ring

theorem goldbach_general_coefficient_of_coprime_zero (q k : ℕ) [NeZero q] [NeZero k]
    (hqk : q.Coprime k) (ℓ b n : ℤ) (hℓ : (ℓ:ZMod q)=0) :
    generalCoefficient q k ℓ b n=cohenCorrelation q n/(q.totient:ℂ) := by
  classical
  have : Subsingleton (ZMod (q.gcd k)) := by rw [hqk.gcd_eq_one];infer_instance
  have hP (v : (ZMod q)ˣ) :
      ZMod.castHom (Nat.gcd_dvd_left q k) (ZMod (q.gcd k)) (v:ZMod q)=(b:ZMod (q.gcd k)) :=
    Subsingleton.elim _ _
  rw [generalCoefficient_as_quadratic]
  simp_rw [ite_eq_left (hP _),hℓ,zero_mul,sub_zero]
  rw [sum_const,card_univ,nsmul_eq_mul,ZMod.card_units_eq_totient,hqk.gcd_eq_one,
    Nat.totient_one,Nat.cast_one,cohenCorrelation_eq]
  have hφ : (q.totient:ℂ)≠0 := by exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  field_simp

theorem goldbach_odd_prime_cohen_norm (p : ℕ) [Fact p.Prime] (hp2 : p≠2) (n : ℤ) :
    ‖cohenCorrelation p n‖≤(p:ℝ)+1 := by
  have he : cohenCorrelation p n=oddCohenFactor p n := by
    simpa only [pow_one,ite_true,one_mul] using cohenCorrelation_odd_prime_pow p hp2 1 (by decide) n
  rw [he]
  exact norm_oddCohenFactor_le p n

theorem goldbach_general_coefficient_odd_prime_bound (p k ℓ : ℕ)
    [Fact p.Prime] [NeZero k] (hp2 : p≠2) (b n : ℤ) (hb : IsCoprime (k:ℤ) b) :
    ‖generalCoefficient p k (ℓ:ℤ) b n‖≤8*(p.gcd (k*ℓ):ℝ)/(p:ℝ) := by
  have hp : p.Prime := Fact.out
  have hp3 : (3:ℝ)≤p := by exact_mod_cast (show 3≤p by have := hp.two_le;omega)
  have hp0 : (0:ℝ)<p := by linarith
  have hp1 : 0<(p:ℝ)-1 := by linarith
  have hφ : (p.totient:ℝ)=(p:ℝ)-1 := by
    simp only [Nat.totient_prime hp,Nat.cast_sub hp.one_le,Nat.cast_one]
  have hB₁ (m : ℤ) : ‖cohenCorrelation p m/(p.totient:ℂ)‖≤8 := by
    rw [norm_div,Complex.norm_natCast,hφ]
    apply (div_le_div_of_nonneg_right (goldbach_odd_prime_cohen_norm p hp2 m) hp1.le).trans
    exact (div_le_iff₀ hp1).mpr (by linarith)
  have hB₂ : ‖(μ p:ℂ)*cohenCorrelation p n/(p.totient:ℂ)^2‖≤8/(p:ℝ) := by
    rw [ArithmeticFunction.moebius_apply_prime hp]
    simp only [Int.cast_neg,Int.cast_one,neg_one_mul,norm_div,norm_neg,norm_pow,Complex.norm_natCast,hφ]
    apply (div_le_div_of_nonneg_right (goldbach_odd_prime_cohen_norm p hp2 n) (sq_nonneg _)).trans
    apply (div_le_div_iff₀ (sq_pos_of_pos hp1) hp0).mpr
    nlinarith
  by_cases hk : p∣k
  · have hbu : IsUnit (b:ZMod p) := (ZMod.coe_int_isUnit_iff_isCoprime b p).mpr
      (integer_coprime_of_nat_dvd p k b hb hk)
    rw [goldbach_general_coefficient_of_dvd p k hk (ℓ:ℤ) b n hbu,
      Nat.gcd_eq_left_iff_dvd.mpr (hk.mul_right ℓ)]
    apply (hB₁ _).trans_eq
    field_simp
  · have hpk : p.Coprime k := (hp.coprime_iff_not_dvd).mpr hk
    by_cases hℓ : p∣ℓ
    · have hz : ((ℓ:ℤ):ZMod p)=0 := by
        simpa only [Int.cast_natCast] using (ZMod.natCast_eq_zero_iff ℓ p).mpr hℓ
      rw [goldbach_general_coefficient_of_coprime_zero p k hpk (ℓ:ℤ) b n hz,
        Nat.gcd_eq_left_iff_dvd.mpr (hℓ.mul_left k)]
      apply (hB₁ _).trans_eq
      field_simp
    · have hpl : p.Coprime ℓ := (hp.coprime_iff_not_dvd).mpr hℓ
      have hu : IsUnit ((ℓ:ℤ):ZMod p) := by
        simpa only [Int.cast_natCast] using (ZMod.isUnit_iff_coprime ℓ p).mpr hpl.symm
      rw [goldbach_general_coefficient_of_coprime_unit p k hpk (ℓ:ℤ) b n hu,
        (hpk.mul_right hpl).gcd_eq_one,Nat.cast_one,mul_one]
      exact hB₂

end PrimeSquares

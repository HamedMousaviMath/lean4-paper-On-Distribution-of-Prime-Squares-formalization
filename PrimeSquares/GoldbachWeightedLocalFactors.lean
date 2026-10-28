import PrimeSquares.GoldbachLowerProductBounds

set_option autoImplicit false
open Finset
namespace PrimeSquares

noncomputable def goldbachJointLocalReal (p : ℕ) (n : ℤ) : ℝ :=
  (p:ℝ)*((p:ℝ)-1-(goldbachRho p n:ℝ)-(goldbachRho p (n-1):ℝ))/((p:ℝ)-1)^2

noncomputable def goldbachWeightedPrimeValue (R : ℝ) (n : ℤ) (p : ℕ) : ℝ :=
  if p%4=1 then
    if (p:ℝ)≤R then
      (goldbachRho p (n-1):ℝ)*((p:ℝ)-1)/
        ((p:ℝ)-1-(goldbachRho p n:ℝ)-(goldbachRho p (n-1):ℝ))
    else ((p:ℝ)-1)/((p:ℝ)-2)
  else 0

noncomputable def goldbachWeightedMultiplicative (R : ℝ) (n : ℤ) (u : ℕ) : ℝ :=
  if u=0 then 0 else ∏ p∈u.primeFactors,goldbachWeightedPrimeValue R n p

noncomputable def goldbachWeightedB (R : ℝ) (n : ℤ) : ℝ :=
  ∏ p∈goldbachLargeLocalPrimes R,goldbachJointLocalReal p n

noncomputable def goldbachWeightedC (R : ℝ) (n : ℤ) : ℝ :=
  goldbachWeightedB R n * ∏ p∈goldbachLargeLocalPrimes R,
    (1+goldbachWeightedPrimeValue R n p/((p:ℝ)-1))

theorem goldbach_joint_denominator_positive {p : ℕ} (hp : p.Prime) (hp3 : 3<p) (n : ℤ) :
    0<(p:ℝ)-1-(goldbachRho p n:ℝ)-(goldbachRho p (n-1):ℝ) := by
  have : Fact p.Prime := ⟨hp⟩
  by_cases hp5 : p=5
  · subst p
    have hr : (goldbachRho 5 (n-1):ℝ)≤2 := by
      exact_mod_cast goldbach_rho_le_two 5 (by decide) (n-1)
    rcases goldbach_rho_five_consecutive n with h|⟨h,h'⟩
    · simp only [h,Nat.cast_zero,Nat.cast_ofNat];linarith
    · simp only [h,h',Nat.cast_zero,Nat.cast_ofNat];norm_num
  · have h4 : p≠4 := by intro h;exact (by decide : ¬Nat.Prime 4) (h ▸ hp)
    have h6 : p≠6 := by intro h;exact (by decide : ¬Nat.Prime 6) (h ▸ hp)
    have hpR : (7:ℝ)≤p := by exact_mod_cast (show 7≤p by omega)
    have h₀ : (goldbachRho p n:ℝ)≤2 := by exact_mod_cast goldbach_rho_le_two p (by omega) n
    have h₁ : (goldbachRho p (n-1):ℝ)≤2 := by exact_mod_cast goldbach_rho_le_two p (by omega) (n-1)
    linarith

theorem goldbach_joint_local_positive {p : ℕ} (hp : p.Prime) (hp3 : 3<p) (n : ℤ) :
    0<goldbachJointLocalReal p n := by
  have hpR : (3:ℝ)<p := by exact_mod_cast hp3
  exact div_pos (mul_pos (by linarith) (goldbach_joint_denominator_positive hp hp3 n))
    (sq_pos_of_pos (by linarith))

theorem goldbach_weighted_prime_nonneg (R : ℝ) (n : ℤ) {p : ℕ} (hp : p.Prime) :
    0≤goldbachWeightedPrimeValue R n p := by
  unfold goldbachWeightedPrimeValue
  split_ifs with h4 hR
  · have hp3 : 3<p := by have := hp.two_le;omega
    have hpR : (3:ℝ)<p := by exact_mod_cast hp3
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (by linarith))
      (goldbach_joint_denominator_positive hp hp3 n).le
  · have hp3 : 3<p := by have := hp.two_le;omega
    have hpR : (3:ℝ)<p := by exact_mod_cast hp3
    exact div_nonneg (by linarith) (by linarith)
  · exact le_refl 0

theorem goldbach_weighted_prime_le_six (R : ℝ) (n : ℤ) {p : ℕ} (hp : p.Prime) :
    goldbachWeightedPrimeValue R n p≤6 := by
  have : Fact p.Prime := ⟨hp⟩
  unfold goldbachWeightedPrimeValue
  split_ifs with h4 hR
  · have hp3 : 3<p := by have := hp.two_le;omega
    apply (div_le_iff₀ (goldbach_joint_denominator_positive hp hp3 n)).mpr
    have hr : (goldbachRho p (n-1):ℝ)≤2 := by exact_mod_cast goldbach_rho_le_two p (by omega) (n-1)
    by_cases hp5 : p=5
    · subst p
      rcases goldbach_rho_five_consecutive n with h|⟨h,h'⟩
      · simp only [h,Nat.cast_zero,Nat.cast_ofNat];nlinarith
      · simp only [h,h',Nat.cast_zero,Nat.cast_ofNat];norm_num
    · have hpR : (7:ℝ)≤p := by exact_mod_cast (show 7≤p by omega)
      have hr' : (goldbachRho p n:ℝ)≤2 := by exact_mod_cast goldbach_rho_le_two p (by omega) n
      nlinarith [mul_nonneg (sub_nonneg.mpr hr) (show 0≤(p:ℝ)-1 by linarith)]
  · have hpR : (5:ℝ)≤p := by exact_mod_cast (show 5≤p by have := hp.two_le;omega)
    apply (div_le_iff₀ (by linarith : 0<(p:ℝ)-2)).mpr
    linarith
  · norm_num

theorem goldbach_weighted_small_prime_cancel {p : ℕ} (hp : p.Prime) (hp3 : 3<p)
    (R : ℝ) (hpR : (p:ℝ)≤R) (n : ℤ) (hp4 : p%4=1) :
    goldbachJointLocalReal p n*(1+goldbachWeightedPrimeValue R n p/((p:ℝ)-1))=
      goldbachUnrestrictedLocalReal p n ∧
    goldbachJointLocalReal p n*goldbachWeightedPrimeValue R n p=
      (p:ℝ)*(goldbachRho p (n-1):ℝ)/((p:ℝ)-1) := by
  have hpR' : (3:ℝ)<p := by exact_mod_cast hp3
  have hden := (goldbach_joint_denominator_positive hp hp3 n).ne'
  have hp1 : (p:ℝ)-1≠0 := by linarith
  unfold goldbachJointLocalReal goldbachWeightedPrimeValue goldbachUnrestrictedLocalReal
  rw [ite_eq_left hp4,ite_eq_left hpR]
  constructor
  · field_simp;ring
  · field_simp

theorem goldbach_weighted_lower_local_cancel {p : ℕ} (hp : p.Prime) (hp3 : 3<p)
    (R : ℝ) (hpR : (p:ℝ)≤R) (n : ℤ) :
    goldbachUnrestrictedLocalReal p n*(1-goldbachLowerDensity R n p)=
      goldbachJointLocalReal p n := by
  have : Fact p.Prime := ⟨hp⟩
  have hpR' : (3:ℝ)<p := by exact_mod_cast hp3
  have hd := (goldbach_local_denominator_pos p hp3 n).ne'
  have hp1 : (p:ℝ)-1≠0 := by linarith
  unfold goldbachUnrestrictedLocalReal goldbachLowerDensity goldbachLocalDensity goldbachJointLocalReal
  rw [ite_eq_left hpR]
  field_simp

theorem goldbach_weighted_upper_local_cancel {p : ℕ} (hp : p.Prime) (hp3 : 3<p)
    (R : ℝ) (hpR : (p:ℝ)≤R) (n : ℤ) :
    goldbachUnrestrictedLocalReal p (n-1)*(1-goldbachUpperDensity R n p)=
      goldbachJointLocalReal p n := by
  have : Fact p.Prime := ⟨hp⟩
  have hpR' : (3:ℝ)<p := by exact_mod_cast hp3
  have hd := (goldbach_local_denominator_pos p hp3 (n-1)).ne'
  have hp1 : (p:ℝ)-1≠0 := by linarith
  unfold goldbachUnrestrictedLocalReal goldbachUpperDensity goldbachLocalDensity goldbachJointLocalReal
  rw [ite_eq_left hpR]
  field_simp
  ring

theorem goldbach_weighted_multiplicative_one (R : ℝ) (n : ℤ) :
    goldbachWeightedMultiplicative R n 1=1 := by simp [goldbachWeightedMultiplicative]

theorem goldbach_weighted_multiplicative_nonneg (R : ℝ) (n : ℤ) (u : ℕ) :
    0≤goldbachWeightedMultiplicative R n u := by
  classical
  unfold goldbachWeightedMultiplicative
  split_ifs
  · exact le_refl 0
  · exact prod_nonneg (fun p hp=>goldbach_weighted_prime_nonneg R n (Nat.prime_of_mem_primeFactors hp))

theorem goldbach_weighted_multiplicative_mul (R : ℝ) (n : ℤ) (a b : ℕ) (hc : a.Coprime b) :
    goldbachWeightedMultiplicative R n (a*b)=
      goldbachWeightedMultiplicative R n a*goldbachWeightedMultiplicative R n b := by
  classical
  by_cases ha : a=0
  · simp [ha,goldbachWeightedMultiplicative]
  by_cases hb : b=0
  · simp [hb,goldbachWeightedMultiplicative]
  simp only [goldbachWeightedMultiplicative,ha,hb,mul_ne_zero ha hb,ite_false,
    Nat.primeFactors_mul ha hb,prod_union hc.disjoint_primeFactors]

theorem goldbach_weighted_B_positive (R : ℝ) (hR : 0≤R) (n : ℤ) :
    0<goldbachWeightedB R n := by
  classical
  exact prod_pos (fun p hp=>goldbach_joint_local_positive
    ((mem_goldbach_large_local_primes hR p).mp hp).1
    ((mem_goldbach_large_local_primes hR p).mp hp).2.1 n)

theorem goldbach_weighted_B_le_C (R : ℝ) (hR : 0≤R) (n : ℤ) :
    goldbachWeightedB R n≤goldbachWeightedC R n := by
  classical
  have hp : (1:ℝ)≤∏ p∈goldbachLargeLocalPrimes R,
      (1+goldbachWeightedPrimeValue R n p/((p:ℝ)-1)) := by
    apply le_trans (show (1:ℝ)≤∏ _p∈goldbachLargeLocalPrimes R,(1:ℝ) by simp)
    apply prod_le_prod₀
    · intro p hp;norm_num
    intro p hp
    have hs := (mem_goldbach_large_local_primes hR p).mp hp
    have hpR : (3:ℝ)<p := by exact_mod_cast hs.2.1
    have := div_nonneg (goldbach_weighted_prime_nonneg R n hs.1) (by linarith : 0≤(p:ℝ)-1)
    linarith
  exact le_mul_of_one_le_right (goldbach_weighted_B_positive R hR n).le hp

theorem goldbach_weighted_C_positive (R : ℝ) (hR : 0≤R) (n : ℤ) :
    0<goldbachWeightedC R n :=
  (goldbach_weighted_B_positive R hR n).trans_le (goldbach_weighted_B_le_C R hR n)

end PrimeSquares

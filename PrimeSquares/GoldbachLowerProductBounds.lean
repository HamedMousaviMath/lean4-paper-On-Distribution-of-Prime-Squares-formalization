import PrimeSquares.GoldbachLowerSieveApplication

set_option autoImplicit false
open Finset
namespace PrimeSquares

noncomputable def goldbachUnrestrictedLocalReal (p : ℕ) (n : ℤ) : ℝ :=
  (p:ℝ)*((p:ℝ)-1-(goldbachRho p n:ℝ))/((p:ℝ)-1)^2

theorem goldbach_unrestricted_local_real_positive {p : ℕ} (hp : p.Prime)
    (hp3 : 3<p) (n : ℤ) : 0<goldbachUnrestrictedLocalReal p n := by
  have : Fact p.Prime := ⟨hp⟩
  have hpR : (3:ℝ)<p := by exact_mod_cast hp3
  exact div_pos (mul_pos (by linarith) (goldbach_local_denominator_pos p hp3 n))
    (sq_pos_of_pos (by linarith))

theorem goldbach_unrestricted_local_majorant {p : ℕ} (hp : p.Prime)
    (hp7 : 7≤p) (n : ℤ) :
    1-2/((p:ℝ)-3)≤goldbachUnrestrictedLocalReal p n := by
  have : Fact p.Prime := ⟨hp⟩
  have hpR : (7:ℝ)≤p := by exact_mod_cast hp7
  have hr : (goldbachRho p n:ℝ)≤2 := by exact_mod_cast goldbach_rho_le_two p (by omega) n
  have hnum : 0≤(p:ℝ) := Nat.cast_nonneg _
  have h₁ : 0<(p:ℝ)-3 := by linarith
  have h₂ : 0<((p:ℝ)-1)^2 := sq_pos_of_pos (by linarith)
  unfold goldbachUnrestrictedLocalReal
  apply (le_div_iff₀ h₂).mpr
  apply (mul_le_mul_iff_left₀ h₁).mp
  field_simp
  nlinarith [mul_nonneg (sub_nonneg.mpr hr) hnum,sq_nonneg ((p:ℝ)-1)]

theorem goldbach_unrestricted_local_five (n : ℤ) :
    (1:ℝ)/2≤goldbachUnrestrictedLocalReal 5 n := by
  have : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hr : (goldbachRho 5 n:ℝ)≤2 := by exact_mod_cast goldbach_rho_le_two 5 (by decide) n
  unfold goldbachUnrestrictedLocalReal
  norm_num
  linarith

theorem goldbach_lower_arithmetic_real_product (R : ℝ) (hR : 3≤R) (n : ℤ)
    (hn : (n:ZMod 24)=12) :
    (goldbachArithmeticFactor R 24 1 11 n).re=
      24*∏ p∈goldbachLargeLocalPrimes R,goldbachUnrestrictedLocalReal p n := by
  have hphase : ((n-(1:ℤ)*11:ℤ):ZMod 24)=1 := by norm_num [hn]
  have he := goldbach_arithmetic_factor_large_primes R hR 24 1 (by decide) 11 n (by decide) hphase
  simp only [Nat.cast_one] at he
  have hf : goldbachArithmeticFactor R 24 1 11 n=
      ((24*∏ p∈goldbachLargeLocalPrimes R,goldbachUnrestrictedLocalReal p n:ℝ):ℂ) := by
    rw [he]
    push_cast
    congr 1
    apply prod_congr rfl
    intro p hp
    obtain ⟨hprime,hlarge,_⟩ := (mem_goldbach_large_local_primes (by linarith) p).mp hp
    have : Fact p.Prime := ⟨hprime⟩
    dsimp only [goldbachUnrestrictedLocalReal]
    push_cast
    exact goldbach_prime_unrestricted_factor p 24
      (goldbach_large_prime_coprime_twentyfour p hprime hlarge) 1 11 n (by simp)
  rw [hf,Complex.ofReal_re]

theorem goldbach_lower_theta_inverse (K R z : ℝ) (hz : 2<z)
    (hM : GoldbachClassicalIntervalMertens K) (n : ℕ) :
    (goldbachLowerTheta R z n)⁻¹≤(1+K/Real.log 2)*(Real.log z/Real.log 2)^2 := by
  classical
  let S := goldbachLowerSievePrimes z
  have hS : ∀ p∈S,p.Prime ∧ 7≤p ∧ (2:ℝ)≤p ∧ (p:ℝ)<z := by
    intro p hp
    have hs := (mem_goldbach_lower_sieve_primes z p).mp hp
    have h7 := goldbach_lower_prime_ge_seven hs.1
    exact ⟨hs.1.1,h7,by exact_mod_cast (show 2≤p by omega),hs.2⟩
  have hprod : (∏ p∈S,(1-goldbachLowerDensity R n p)⁻¹)≤
      ∏ p∈S,(1-2/((p:ℝ)-3))⁻¹ := by
    apply prod_le_prod₀
    · intro p hp
      exact inv_nonneg.mpr (sub_pos.mpr (goldbach_lower_prime_density_range R n
        ((mem_goldbach_lower_sieve_primes z p).mp hp).1).2).le
    · intro p hp
      have hs := hS p hp
      have : Fact p.Prime := ⟨hs.1⟩
      have hb := goldbach_local_density_le R p (by omega) ((n:ℤ)-1) n
      have hpos : 0<1-2/((p:ℝ)-3) := sub_pos.mpr (goldbach_density_bound_lt_one p hs.2.1)
      simpa only [goldbachLowerDensity,one_div] using
        one_div_le_one_div_of_le hpos (sub_le_sub_left hb 1)
  have hm := hM.preliminary 2 z S le_rfl hz hS
  simpa only [Real.rpow_two,prod_inv_distrib,goldbachLowerTheta] using hprod.trans hm

theorem goldbach_lower_arithmetic_polylog (K R : ℝ) (hK : 0≤K) (hR : 5≤R)
    (hM : GoldbachClassicalIntervalMertens K) (n : ℤ) (hn : (n:ZMod 24)=12) :
    12/((1+K/Real.log 2)*(Real.log (R+1)/Real.log 2)^2)≤
      (goldbachArithmeticFactor R 24 1 11 n).re := by
  classical
  let S := (goldbachLargeLocalPrimes R).erase 5
  let V := ∏ p∈S,(1-2/((p:ℝ)-3))
  have h5 : 5∈goldbachLargeLocalPrimes R :=
    (mem_goldbach_large_local_primes (by linarith) 5).mpr ⟨by decide,by decide,hR⟩
  have hS : ∀ p∈S,p.Prime ∧ 7≤p ∧ (2:ℝ)≤p ∧ (p:ℝ)<R+1 := by
    intro p hp
    obtain ⟨hp5,hp⟩ := mem_erase.mp hp
    obtain ⟨hprime,hlarge,hpR⟩ := (mem_goldbach_large_local_primes (by linarith) p).mp hp
    have hp4 : p≠4 := by intro hh; subst p; exact (by decide : ¬Nat.Prime 4) hprime
    have hp6 : p≠6 := by intro hh; subst p; exact (by decide : ¬Nat.Prime 6) hprime
    have h7 : 7≤p := by omega
    exact ⟨hprime,h7,by exact_mod_cast (show 2≤p by omega),by linarith⟩
  have hV : 0<V := prod_pos (fun p hp=>sub_pos.mpr (goldbach_density_bound_lt_one p (hS p hp).2.1))
  have hprod : V≤∏ p∈S,goldbachUnrestrictedLocalReal p n := by
    apply prod_le_prod₀
    · intro p hp
      exact (sub_pos.mpr (goldbach_density_bound_lt_one p (hS p hp).2.1)).le
    · intro p hp
      exact goldbach_unrestricted_local_majorant (hS p hp).1 (hS p hp).2.1 n
  have hG : 12*V≤(goldbachArithmeticFactor R 24 1 11 n).re := by
    rw [goldbach_lower_arithmetic_real_product R (by linarith) n hn,
      ←mul_prod_erase (goldbachLargeLocalPrimes R) (goldbachUnrestrictedLocalReal · n) h5]
    have hh := mul_le_mul (goldbach_unrestricted_local_five n) hprod hV.le
      (goldbach_unrestricted_local_real_positive (by decide : Nat.Prime 5) (by decide) n).le
    nlinarith only [hh]
  have hm : V⁻¹≤(1+K/Real.log 2)*(Real.log (R+1)/Real.log 2)^2 := by
    simpa only [V,prod_inv_distrib,Real.rpow_two] using
      hM.preliminary 2 (R+1) S le_rfl (by linarith) hS
  have hL : 0<(1+K/Real.log 2)*(Real.log (R+1)/Real.log 2)^2 := by
    have := Real.log_pos (by norm_num : (1:ℝ)<2)
    have := Real.log_pos (by linarith : 1<R+1)
    positivity
  apply (div_le_iff₀ hL).mpr
  have hh := (inv_le_iff_one_le_mul₀ hV).mp hm
  nlinarith only [mul_le_mul_of_nonneg_left hG hL.le,hh]

end PrimeSquares

import PrimeSquares.GoldbachWeightedLocalFactors

set_option autoImplicit false
open Finset
namespace PrimeSquares

noncomputable def goldbachUpperBaseResidue (ℓ : ℕ) : ℕ := by
  classical
  exact if h : (ℓ/2).Coprime 6 then
    Classical.choose (goldbach_upper_sieve_residue (ℓ/2) 1 h (by decide) (by simp)) else 1

noncomputable def goldbachUpperArithmeticReal (p ℓ : ℕ) (n : ℤ) : ℝ :=
  if p∣ℓ then (p:ℝ)*(goldbachRho p (n-1):ℝ)/((p:ℝ)-1)
  else goldbachUnrestrictedLocalReal p (n-1)

noncomputable def goldbachUpperSievePrimes (ℓ : ℕ) (z : ℝ) : Finset ℕ := by
  classical
  exact (range (Nat.ceil z)).filter (GoldbachFixedUpperSievePrime ℓ)

noncomputable def goldbachUpperTheta (R z : ℝ) (ℓ : ℕ) (n : ℤ) : ℝ :=
  ∏ p∈goldbachUpperSievePrimes ℓ z,(1-goldbachUpperDensity R n p)

noncomputable def goldbachUpperMainTerm (ψ : SchwartzMap ℝ ℝ) (N : ℕ) (R : ℝ) (ℓ n : ℕ) : ℝ :=
  (goldbachArithmeticFactor R 12 (ℓ:ℤ) (goldbachUpperBaseResidue ℓ:ℤ) ((n:ℤ)-1)/
    ((ℓ:ℂ)*((12:ℕ).totient:ℂ))*
      goldbachSingularIntegral ψ N ℓ R ((n:ℝ)-1) (N:ℝ) ((N:ℝ)^2)).re

theorem goldbach_upper_base_residue (v : ℕ) (hv : v.Coprime 6) :
    (goldbachUpperBaseResidue (2*v)).Coprime 12 ∧
      (v:ZMod 12)*(goldbachUpperBaseResidue (2*v):ZMod 12)=5 := by
  classical
  have hd : 2*v/2=v := by omega
  have he : goldbachUpperBaseResidue (2*v)=
      Classical.choose (goldbach_upper_sieve_residue v 1 hv (by decide) (by simp)) := by
    simp only [goldbachUpperBaseResidue,hd,dite_eq_left hv]
  obtain ⟨haBound,hva,_,ha⟩ := Classical.choose_spec
    (goldbach_upper_sieve_residue v 1 hv (by decide) (by simp))
  rw [←he] at hva ha
  refine ⟨by simpa only [mul_one] using ha,?_⟩
  have hh := (ZMod.natCast_eq_natCast_iff (v*goldbachUpperBaseResidue (2*v)) 5 12).mpr hva
  simpa only [Nat.cast_mul,Nat.cast_ofNat] using hh

theorem mem_goldbach_upper_sieve_primes (ℓ : ℕ) (z : ℝ) (p : ℕ) :
    p∈goldbachUpperSievePrimes ℓ z ↔ GoldbachFixedUpperSievePrime ℓ p ∧ (p:ℝ)<z := by
  classical
  simp only [goldbachUpperSievePrimes,mem_filter,mem_range,Nat.lt_ceil]
  exact and_comm

theorem goldbach_upper_arithmetic_factor_real {p : ℕ} (hp : p.Prime) (hp3 : 3<p)
    (ℓ : ℕ) (a n : ℤ) :
    1+generalCoefficient p 12 (ℓ:ℤ) a (n-1)=(goldbachUpperArithmeticReal p ℓ n:ℂ) := by
  have : Fact p.Prime := ⟨hp⟩
  have hcop : p.Coprime 12 := Nat.Coprime.of_dvd_right (by decide : 12∣24)
    (goldbach_large_prime_coprime_twentyfour p hp hp3)
  by_cases hd : p∣ℓ
  · have hz : ((ℓ:ℤ):ZMod p)=0 := by
      simpa only [Int.cast_natCast] using (ZMod.natCast_eq_zero_iff ℓ p).mpr hd
    rw [goldbach_prime_zero_multiplier_factor p 12 hcop (ℓ:ℤ) a (n-1) hz]
    simp only [goldbachUpperArithmeticReal,ite_eq_left hd,Complex.ofReal_div,
      Complex.ofReal_mul,Complex.ofReal_natCast,Complex.ofReal_sub,Complex.ofReal_one]
  · have hu : IsUnit ((ℓ:ℤ):ZMod p) := by
      apply isUnit_iff_ne_zero.mpr
      intro hz
      exact hd ((ZMod.natCast_eq_zero_iff ℓ p).mp (by simpa only [Int.cast_natCast] using hz))
    rw [goldbach_prime_unrestricted_factor p 12 hcop (ℓ:ℤ) a (n-1) hu]
    simp only [goldbachUpperArithmeticReal,ite_eq_right hd,goldbachUnrestrictedLocalReal,
      Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_natCast,Complex.ofReal_sub,
      Complex.ofReal_one,Complex.ofReal_pow]

theorem goldbach_upper_arithmetic_real_nonneg {p : ℕ} (hp : p.Prime) (hp3 : 3<p)
    (ℓ : ℕ) (n : ℤ) : 0≤goldbachUpperArithmeticReal p ℓ n := by
  unfold goldbachUpperArithmeticReal
  split_ifs
  · have hpR : (3:ℝ)<p := by exact_mod_cast hp3
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (by linarith)
  · exact (goldbach_unrestricted_local_real_positive hp hp3 (n-1)).le

theorem goldbach_upper_arithmetic_real_product (R : ℝ) (hR : 3≤R)
    (v : ℕ) (hv : v.Coprime 6) (n : ℤ) (hn : (n:ZMod 24)=12) :
    goldbachArithmeticFactor R 12 ((2*v:ℕ):ℤ) (goldbachUpperBaseResidue (2*v):ℤ) (n-1)=
      ((24*∏ p∈goldbachLargeLocalPrimes R,goldbachUpperArithmeticReal p (2*v) n:ℝ):ℂ) := by
  classical
  obtain ⟨ha,hva⟩ := goldbach_upper_base_residue v hv
  have hac : IsCoprime (12:ℤ) (goldbachUpperBaseResidue (2*v):ℤ) := by
    exact_mod_cast ha.symm
  have hphase := goldbach_upper_phase_twentyfour v (goldbachUpperBaseResidue (2*v):ℤ) n
    (by simpa only [Int.cast_natCast] using hva) hn
  rw [goldbach_arithmetic_factor_large_primes R hR 12 (2*v) ⟨v,by ring⟩
    (goldbachUpperBaseResidue (2*v):ℤ) (n-1) hac hphase]
  push_cast
  congr 1
  apply prod_congr rfl
  intro p hp
  obtain ⟨hprime,hlarge,_⟩ := (mem_goldbach_large_local_primes (by linarith) p).mp hp
  exact goldbach_upper_arithmetic_factor_real hprime hlarge (2*v) _ n

theorem goldbach_weighted_lower_small_product (R : ℝ) (hR : 3≤R) (n : ℤ)
    (hn : (n:ZMod 24)=12) :
    (goldbachArithmeticFactor R 24 1 11 n).re*
      (∏ p∈goldbachLargeLocalPrimes R,if p%4=3 then 1-goldbachLowerDensity R n p else 1)=
      24*goldbachWeightedC R n := by
  classical
  rw [goldbach_lower_arithmetic_real_product R hR n hn]
  unfold goldbachWeightedC goldbachWeightedB
  rw [mul_assoc,←prod_mul_distrib,←prod_mul_distrib]
  congr 1
  apply prod_congr rfl
  intro p hp
  obtain ⟨hprime,hlarge,hpR⟩ := (mem_goldbach_large_local_primes (by linarith) p).mp hp
  by_cases h4 : p%4=1
  · have h43 : p%4≠3 := by omega
    rw [ite_eq_right h43,mul_one]
    exact (goldbach_weighted_small_prime_cancel hprime hlarge R hpR n h4).1.symm
  · have h43 : p%4=3 := by have := hprime.eq_two_or_odd;omega
    rw [ite_eq_left h43,goldbach_weighted_lower_local_cancel hprime hlarge R hpR n]
    simp only [goldbachWeightedPrimeValue,ite_eq_right h4,zero_div,add_zero,mul_one]

theorem goldbach_upper_theta_positive (R z : ℝ) (ℓ : ℕ) (n : ℤ) :
    0<goldbachUpperTheta R z ℓ n := by
  classical
  apply prod_pos
  intro p hp
  obtain ⟨⟨hprime,hnot⟩,_⟩ := (mem_goldbach_upper_sieve_primes ℓ z p).mp hp
  have hp3 : 3<p := by
    have := hprime.two_le
    by_contra! hh
    have he : p=2 ∨ p=3 := by omega
    rcases he with he|he <;> apply hnot <;> rw [he] <;> omega
  have : Fact p.Prime := ⟨hprime⟩
  exact sub_pos.mpr (goldbach_upper_density_range R p hp3 n).2

end PrimeSquares

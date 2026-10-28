import PrimeSquares.GoldbachSieveSmallFactors
import PrimeSquares.GoldbachSieveResidueFactors
import PrimeSquares.GoldbachSieveDensityBounds

set_option autoImplicit false
open Finset
namespace PrimeSquares

theorem goldbach_prime_local_density_ratio (R : ℝ) (p k : ℕ)
    [Fact p.Prime] [NeZero k] (hp : 3 < p) (hpR : (p:ℝ)≤R)
    (hpk : p.Coprime k) (ℓ b n c : ℤ)
    (hℓ : IsUnit (ℓ:ZMod p)) (hb : IsCoprime ((k*p:ℕ):ℤ) b)
    (hbc : (ℓ:ZMod p)*(b:ZMod p)=(c:ZMod p)) :
    1+generalCoefficient p (k*p) ℓ b n=
      (1+generalCoefficient p k ℓ b n)*
        (((p:ℂ)-1)*(goldbachLocalDensity R p (n-c) n:ℂ)) := by
  have hprime : p.Prime := Fact.out
  have hbu : IsUnit (b:ZMod p) := (ZMod.coe_int_isUnit_iff_isCoprime b p).mpr
    (integer_coprime_of_nat_dvd p (k*p) b hb (dvd_mul_left p k))
  have hr : goldbachRho p (n-ℓ*b)=goldbachRho p (n-c) :=
    goldbach_rho_congr p (by simp only [Int.cast_sub,Int.cast_mul];rw [hbc])
  have hp1 : (p:ℂ)-1≠0 := sub_ne_zero.mpr (by exact_mod_cast hprime.ne_one)
  have hden : (p:ℂ)-1-(goldbachRho p n:ℂ)≠0 := by
    have hh := (goldbach_local_denominator_pos p hp n).ne'
    exact_mod_cast hh
  rw [goldbach_prime_fixed_factor p (k*p) (dvd_mul_left p k) ℓ b n hbu,hr,
    goldbach_prime_unrestricted_factor p k hpk ℓ b n hℓ,
    goldbachLocalDensity,ite_eq_left hpR]
  push_cast
  field_simp

theorem goldbach_arithmetic_factor_adjoin_prime (R : ℝ) (hR : 3≤R)
    (p k ℓ : ℕ) [Fact p.Prime] [NeZero k] (hp : 3 < p)
    (hpk : p.Coprime k) (h24 : 24∣ℓ*k) (b n c : ℤ)
    (hb : IsCoprime ((k*p:ℕ):ℤ) b) (hn : ((n-(ℓ:ℤ)*b:ℤ):ZMod 24)=1)
    (hℓ : IsUnit ((ℓ:ℤ):ZMod p))
    (hbc : ((ℓ:ℤ):ZMod p)*(b:ZMod p)=(c:ZMod p)) :
    goldbachArithmeticFactor R (k*p) (ℓ:ℤ) b n=
      goldbachArithmeticFactor R k (ℓ:ℤ) b n*
        (((p:ℂ)-1)*(goldbachLocalDensity R p (n-c) n:ℂ)) := by
  classical
  have hb₀ : IsCoprime (k:ℤ) b := integer_coprime_of_nat_dvd k (k*p) b hb (dvd_mul_right k p)
  have h24' : 24∣ℓ*(k*p) := by simpa only [mul_assoc] using h24.mul_right p
  let τ : ℂ := ((p:ℂ)-1)*(goldbachLocalDensity R p (n-c) n:ℂ)
  have hτ : (if p∈goldbachLargeLocalPrimes R then τ else 1)=τ := by
    by_cases hmem : p∈goldbachLargeLocalPrimes R
    · exact ite_eq_left hmem
    · have hpR : ¬(p:ℝ)≤R := by
        intro h
        exact hmem ((mem_goldbach_large_local_primes (by linarith) p).mpr ⟨Fact.out,hp,h⟩)
      rw [ite_eq_right hmem]
      dsimp only [τ,goldbachLocalDensity]
      rw [ite_eq_right hpR]
      push_cast
      have hp1 : (p:ℂ)-1≠0 := sub_ne_zero.mpr (by exact_mod_cast (Fact.out : p.Prime).ne_one)
      field_simp
  have hfactor (q : ℕ) (hq : q∈goldbachLargeLocalPrimes R) :
      1+generalCoefficient q (k*p) (ℓ:ℤ) b n=
        (1+generalCoefficient q k (ℓ:ℤ) b n)*(if q=p then τ else 1) := by
    obtain ⟨hprime,_,hqR⟩ := (mem_goldbach_large_local_primes (by linarith) q).mp hq
    have : Fact q.Prime := ⟨hprime⟩
    by_cases hqp : q=p
    · subst q
      rw [ite_eq_left rfl]
      exact goldbach_prime_local_density_ratio R p k hp hqR hpk (ℓ:ℤ) b n c hℓ hb hbc
    · rw [ite_eq_right hqp,mul_one,goldbach_prime_factor_unchanged q p k hqp (ℓ:ℤ) b n hb]
  calc
    _=24*(∏ q∈goldbachLargeLocalPrimes R,
        (1+generalCoefficient q k (ℓ:ℤ) b n)*(if q=p then τ else 1)) := by
      rw [goldbach_arithmetic_factor_large_primes R hR (k*p) ℓ h24' b n hb hn]
      congr 1
      exact prod_congr rfl hfactor
    _=(24*(∏ q∈goldbachLargeLocalPrimes R,(1+generalCoefficient q k (ℓ:ℤ) b n)))*τ := by
      rw [prod_mul_distrib,prod_ite_eq',hτ]
      ring
    _=_ := by rw [←goldbach_arithmetic_factor_large_primes R hR k ℓ h24 b n hb₀ hn]

theorem goldbach_normalized_factor_adjoin_prime (R : ℝ) (hR : 3≤R)
    (p k ℓ : ℕ) [Fact p.Prime] [NeZero k] (hp : 3 < p)
    (hpk : p.Coprime k) (h24 : 24∣ℓ*k) (b n c : ℤ)
    (hb : IsCoprime ((k*p:ℕ):ℤ) b) (hn : ((n-(ℓ:ℤ)*b:ℤ):ZMod 24)=1)
    (hℓ : IsUnit ((ℓ:ℤ):ZMod p))
    (hbc : ((ℓ:ℤ):ZMod p)*(b:ZMod p)=(c:ZMod p)) :
    goldbachArithmeticFactor R (k*p) (ℓ:ℤ) b n/((k*p).totient:ℂ)=
      goldbachArithmeticFactor R k (ℓ:ℤ) b n/(k.totient:ℂ)*
        (goldbachLocalDensity R p (n-c) n:ℂ) := by
  have hprime : p.Prime := Fact.out
  have hφ : (k.totient:ℂ)≠0 := by exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos k)).ne'
  have hp1 : (p:ℂ)-1≠0 := sub_ne_zero.mpr (by exact_mod_cast hprime.ne_one)
  rw [goldbach_arithmetic_factor_adjoin_prime R hR p k ℓ hp hpk h24 b n c hb hn hℓ hbc,
    Nat.totient_mul hpk.symm,Nat.totient_prime hprime,Nat.cast_mul,
    Nat.cast_sub hprime.one_le,Nat.cast_one]
  field_simp

end PrimeSquares

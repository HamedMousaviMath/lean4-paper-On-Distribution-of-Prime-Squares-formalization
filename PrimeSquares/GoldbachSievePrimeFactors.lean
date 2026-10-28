import PrimeSquares.GoldbachArithmeticPrime
import PrimeSquares.GoldbachSieveRootCounts

set_option autoImplicit false
open scoped ArithmeticFunction.Moebius
namespace PrimeSquares

theorem goldbach_prime_unrestricted_factor (p k : ℕ) [Fact p.Prime] [NeZero k]
    (hpk : p.Coprime k) (ℓ b n : ℤ) (hℓ : IsUnit (ℓ:ZMod p)) :
    1+generalCoefficient p k ℓ b n=
      (p:ℂ)*((p:ℂ)-1-(goldbachRho p n:ℂ))/((p:ℂ)-1)^2 := by
  have hp : p.Prime := Fact.out
  have h1 : (p:ℂ)-1≠0 := by
    have h : (p:ℂ)≠1 := by exact_mod_cast hp.ne_one
    exact sub_ne_zero.mpr h
  rw [goldbach_general_coefficient_of_coprime_unit p k hpk ℓ b n hℓ,
    ArithmeticFunction.moebius_apply_prime hp,Int.cast_neg,Int.cast_one,
    goldbach_cohen_rho,Nat.totient_prime hp,Nat.cast_sub hp.one_le,Nat.cast_one]
  field_simp
  ring

theorem goldbach_prime_fixed_factor (p k : ℕ) [Fact p.Prime] [NeZero k]
    (hpk : p∣k) (ℓ b n : ℤ) (hb : IsUnit (b:ZMod p)) :
    1+generalCoefficient p k ℓ b n=(p:ℂ)*(goldbachRho p (n-ℓ*b):ℂ)/((p:ℂ)-1) := by
  have hp : p.Prime := Fact.out
  have h1 : (p:ℂ)-1≠0 := sub_ne_zero.mpr (by exact_mod_cast hp.ne_one)
  rw [goldbach_general_coefficient_of_dvd p k hpk ℓ b n hb,
    goldbach_cohen_rho,Nat.totient_prime hp,Nat.cast_sub hp.one_le,Nat.cast_one]
  field_simp
  ring

theorem goldbach_prime_zero_multiplier_factor (p k : ℕ) [Fact p.Prime] [NeZero k]
    (hpk : p.Coprime k) (ℓ b n : ℤ) (hℓ : (ℓ:ZMod p)=0) :
    1+generalCoefficient p k ℓ b n=(p:ℂ)*(goldbachRho p n:ℂ)/((p:ℂ)-1) := by
  have hp : p.Prime := Fact.out
  have h1 : (p:ℂ)-1≠0 := sub_ne_zero.mpr (by exact_mod_cast hp.ne_one)
  rw [goldbach_general_coefficient_of_coprime_zero p k hpk ℓ b n hℓ,
    goldbach_cohen_rho,Nat.totient_prime hp,Nat.cast_sub hp.one_le,Nat.cast_one]
  field_simp
  ring

theorem goldbach_prime_unrestricted_count (p k : ℕ) [Fact p.Prime] [NeZero k]
    (hpk : p.Coprime k) (ℓ b n : ℤ) (hℓ : IsUnit (ℓ:ZMod p))
    (hb : IsCoprime (k:ℤ) b) :
    primeSolutionCount p k ℓ b n+goldbachRho p n=p-1 := by
  have hp : p.Prime := Fact.out
  have hp0 : (p:ℂ)≠0 := by exact_mod_cast hp.ne_zero
  have hp1 : (p:ℂ)-1≠0 := sub_ne_zero.mpr (by exact_mod_cast hp.ne_one)
  have h := generalCoefficient_prime_euler_factor p k ℓ b n hb
  rw [goldbach_prime_unrestricted_factor p k hpk ℓ b n hℓ,hpk.gcd_eq_one,
    Nat.totient_one,Nat.cast_one,mul_one] at h
  have hcount : (primeSolutionCount p k ℓ b n:ℂ)=(p:ℂ)-1-(goldbachRho p n:ℂ) := by
    apply (mul_left_cancel₀ (div_ne_zero hp0 (pow_ne_zero 2 hp1)))
    calc
      _=(p:ℂ)*((p:ℂ)-1-(goldbachRho p n:ℂ))/((p:ℂ)-1)^2 := by rw [h]
      _=_ := by ring
  have hh : (primeSolutionCount p k ℓ b n:ℂ)+(goldbachRho p n:ℂ)=((p-1:ℕ):ℂ) := by
    rw [hcount,Nat.cast_sub hp.one_le,Nat.cast_one]
    ring
  exact_mod_cast hh

end PrimeSquares

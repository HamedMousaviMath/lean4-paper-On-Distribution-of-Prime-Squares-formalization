import PrimeSquares.GoldbachSievePrimeFactors
import PrimeSquares.GoldbachArithmeticEuler

set_option autoImplicit false
open Finset
namespace PrimeSquares

theorem goldbach_general_coefficient_residue_congr (q k : ℕ) [NeZero q] [NeZero k]
    (ℓ b a n : ℤ) (hba : (b:ZMod k)=(a:ZMod k)) :
    generalCoefficient q k ℓ b n=generalCoefficient q k ℓ a n := by
  have hh := congrArg (ZMod.castHom (Nat.gcd_dvd_right q k) (ZMod (q.gcd k))) hba
  simp only [map_intCast] at hh
  rw [generalCoefficient_as_quadratic,generalCoefficient_as_quadratic,hh]

theorem goldbach_arithmetic_factor_coefficient_product (R : ℝ) (k : ℕ) [NeZero k]
    (ℓ b n : ℤ) (hb : IsCoprime (k:ℤ) b) :
    goldbachArithmeticFactor R k ℓ b n=generalTwoEulerFactor k ℓ b n*
      ∏ p∈oddPrimesBelow (⌊R⌋₊+1),(1+generalCoefficient p k ℓ b n) := by
  unfold goldbachArithmeticFactor
  congr 1
  apply prod_congr rfl
  intro p hp
  have : Fact p.Prime := ⟨(mem_filter.mp hp).2.1⟩
  exact (generalCoefficient_prime_euler_factor p k ℓ b n hb).symm

theorem goldbach_arithmetic_factor_residue_congr (R : ℝ) (k : ℕ) [NeZero k]
    (ℓ b a n : ℤ) (hb : IsCoprime (k:ℤ) b) (ha : IsCoprime (k:ℤ) a)
    (hba : (b:ZMod k)=(a:ZMod k)) :
    goldbachArithmeticFactor R k ℓ b n=goldbachArithmeticFactor R k ℓ a n := by
  rw [goldbach_arithmetic_factor_coefficient_product R k ℓ b n hb,
    goldbach_arithmetic_factor_coefficient_product R k ℓ a n ha]
  apply congrArg₂ (fun z w : ℂ=>z*w)
  · rw [←generalCoefficient_two_euler_factor,←generalCoefficient_two_euler_factor,
      goldbach_general_coefficient_residue_congr 2 k ℓ b a n hba,
      goldbach_general_coefficient_residue_congr 4 k ℓ b a n hba,
      goldbach_general_coefficient_residue_congr 8 k ℓ b a n hba]
  · apply prod_congr rfl
    intro p hp
    have : Fact p.Prime := ⟨(mem_filter.mp hp).2.1⟩
    rw [goldbach_general_coefficient_residue_congr p k ℓ b a n hba]

theorem goldbach_prime_factor_unchanged (q p k : ℕ) [Fact q.Prime] [Fact p.Prime]
    [NeZero k] (hqp : q≠p) (ℓ b n : ℤ) (hb : IsCoprime ((k*p:ℕ):ℤ) b) :
    generalCoefficient q (k*p) ℓ b n=generalCoefficient q k ℓ b n := by
  have hq : q.Prime := Fact.out
  have hp : p.Prime := Fact.out
  by_cases hqk : q∣k
  · have hqu : IsUnit (b:ZMod q) := (ZMod.coe_int_isUnit_iff_isCoprime b q).mpr
      (integer_coprime_of_nat_dvd q (k*p) b hb (hqk.mul_right p))
    rw [goldbach_general_coefficient_of_dvd q (k*p) (hqk.mul_right p) ℓ b n hqu,
      goldbach_general_coefficient_of_dvd q k hqk ℓ b n hqu]
  · have hqkp : q.Coprime (k*p) := (hq.coprime_iff_not_dvd).mpr (by
      intro h
      rcases hq.dvd_mul.mp h with h|h
      · exact hqk h
      · exact hqp ((Nat.prime_dvd_prime_iff_eq hq hp).mp h))
    have hqk' : q.Coprime k := (hq.coprime_iff_not_dvd).mpr hqk
    by_cases hℓ : (ℓ:ZMod q)=0
    · rw [goldbach_general_coefficient_of_coprime_zero q (k*p) hqkp ℓ b n hℓ,
        goldbach_general_coefficient_of_coprime_zero q k hqk' ℓ b n hℓ]
    · have hu : IsUnit (ℓ:ZMod q) := isUnit_iff_ne_zero.mpr hℓ
      rw [goldbach_general_coefficient_of_coprime_unit q (k*p) hqkp ℓ b n hu,
        goldbach_general_coefficient_of_coprime_unit q k hqk' ℓ b n hu]

end PrimeSquares

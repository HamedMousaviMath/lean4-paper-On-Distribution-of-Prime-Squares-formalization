import PrimeSquares.GoldbachSieveConductor
import PrimeSquares.GoldbachArithmeticEuler
import PrimeSquares.GoldbachSieveRootCounts

set_option autoImplicit false
open Finset
namespace PrimeSquares

theorem goldbach_two_factor_admissible (k ℓ : ℕ) [NeZero k]
    (h8 : 8∣ℓ*k) (b n : ℤ) (hb : IsCoprime (k:ℤ) b)
    (hn : ((n-(ℓ:ℤ)*b:ℤ):ZMod 8)=1) :
    generalTwoEulerFactor k (ℓ:ℤ) b n=8 := by
  rw [←generalCoefficient_two_euler_factor,
    goldbach_general_coefficient_conductor 2 k ℓ ((by decide : 2∣8).trans h8) b n hb,
    goldbach_general_coefficient_conductor 4 k ℓ ((by decide : 4∣8).trans h8) b n hb,
    goldbach_general_coefficient_conductor 8 k ℓ h8 b n hb]
  have h := two_local_partial_eight (n-(ℓ:ℤ)*b)
  rw [ite_eq_left hn,mul_one] at h
  simpa only [show Nat.totient 2=1 by decide,show Nat.totient 4=2 by decide,
    show Nat.totient 8=4 by decide,Nat.cast_one,Nat.cast_ofNat,div_one] using h

theorem goldbach_three_factor_admissible (k ℓ : ℕ) [NeZero k]
    (h3 : 3∣ℓ*k) (b n : ℤ) (hb : IsCoprime (k:ℤ) b)
    (hn : ((n-(ℓ:ℤ)*b:ℤ):ZMod 3)=1) :
    1+generalCoefficient 3 k (ℓ:ℤ) b n=3 := by
  rw [goldbach_general_coefficient_conductor 3 k ℓ h3 b n hb,goldbach_cohen_rho]
  have hr : goldbachRho 3 (n-(ℓ:ℤ)*b)=2 := by
    rw [goldbach_rho_congr 3 (m:=1) (by simpa only [Int.cast_one] using hn),goldbach_rho_eq]
    decide
  rw [hr]
  norm_num [show Nat.totient 3=2 by decide]

noncomputable def goldbachLargeLocalPrimes (R : ℝ) : Finset ℕ :=
  (oddPrimesBelow (⌊R⌋₊+1)).erase 3

theorem mem_goldbach_large_local_primes {R : ℝ} (hR : 0≤R) (p : ℕ) :
    p∈goldbachLargeLocalPrimes R ↔ p.Prime ∧ 3 < p ∧ (p:ℝ)≤R := by
  simp only [goldbachLargeLocalPrimes,mem_erase,oddPrimesBelow,mem_filter,mem_range]
  rw [←goldbach_prime_inclusive_cutoff hR]
  constructor
  · rintro ⟨hp3,hRp,hprime,hp2⟩
    exact ⟨hprime,by omega,hRp⟩
  · rintro ⟨hprime,hp3,hRp⟩
    exact ⟨by omega,hRp,hprime,by omega⟩

theorem goldbach_arithmetic_factor_large_primes (R : ℝ) (hR : 3≤R)
    (k ℓ : ℕ) [NeZero k] (h24 : 24∣ℓ*k) (b n : ℤ)
    (hb : IsCoprime (k:ℤ) b) (hn : ((n-(ℓ:ℤ)*b:ℤ):ZMod 24)=1) :
    goldbachArithmeticFactor R k (ℓ:ℤ) b n=
      24*(∏ p∈goldbachLargeLocalPrimes R,(1+generalCoefficient p k (ℓ:ℤ) b n)) := by
  classical
  have h8 : ((n-(ℓ:ℤ)*b:ℤ):ZMod 8)=1 := by
    have h := congrArg (ZMod.castHom (by decide : 8∣24) (ZMod 8)) hn
    simpa only [map_intCast,map_one] using h
  have h3 : ((n-(ℓ:ℤ)*b:ℤ):ZMod 3)=1 := by
    have h := congrArg (ZMod.castHom (by decide : 3∣24) (ZMod 3)) hn
    simpa only [map_intCast,map_one] using h
  have hprod : (∏ p∈oddPrimesBelow (⌊R⌋₊+1),
      (p:ℂ)*((p.gcd k).totient:ℂ)/((p:ℂ)-1)^2*(primeSolutionCount p k (ℓ:ℤ) b n:ℂ))=
      ∏ p∈oddPrimesBelow (⌊R⌋₊+1),(1+generalCoefficient p k (ℓ:ℤ) b n) := by
    apply prod_congr rfl
    intro p hp
    have : Fact p.Prime := ⟨(mem_filter.mp hp).2.1⟩
    exact (generalCoefficient_prime_euler_factor p k (ℓ:ℤ) b n hb).symm
  have hmem : 3∈oddPrimesBelow (⌊R⌋₊+1) := by
    apply mem_filter.mpr
    refine ⟨mem_range.mpr ((goldbach_prime_inclusive_cutoff (by linarith) 3).mp hR),by decide,by decide⟩
  rw [goldbachArithmeticFactor,hprod,
    goldbach_two_factor_admissible k ℓ ((by decide : 8∣24).trans h24) b n hb h8,
    ←mul_prod_erase (oddPrimesBelow (⌊R⌋₊+1)) (fun p=>1+generalCoefficient p k (ℓ:ℤ) b n) hmem,
    goldbach_three_factor_admissible k ℓ ((by decide : 3∣24).trans h24) b n hb h3]
  unfold goldbachLargeLocalPrimes
  ring

end PrimeSquares

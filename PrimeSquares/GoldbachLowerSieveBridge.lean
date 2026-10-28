import PrimeSquares.GoldbachLowerSieveDensity
import PrimeSquares.GoldbachPositiveSingularComplete

set_option autoImplicit false
open Finset
open scoped SchwartzMap
namespace PrimeSquares

noncomputable def goldbachLowerSieveResidue (d : ℕ) : ℕ := by
  classical
  exact if h : ∀ p : ℕ,p.Prime→p∣d→3<p then
    Classical.choose (goldbach_lower_sieve_residue_from_support d h) else 1

theorem goldbach_lower_residue_properties (d : ℕ)
    (h : ∀ p : ℕ,p.Prime→p∣d→3<p) :
    goldbachLowerSieveResidue d<24*d ∧
      Nat.ModEq 24 (goldbachLowerSieveResidue d) 11 ∧
      Nat.ModEq d (goldbachLowerSieveResidue d) 1 ∧
      (goldbachLowerSieveResidue d).Coprime (24*d) := by
  classical
  simp only [goldbachLowerSieveResidue,dite_eq_left h]
  exact Classical.choose_spec (goldbach_lower_sieve_residue_from_support d h)

theorem goldbach_lower_residue_coprime (d : ℕ) :
    (goldbachLowerSieveResidue d).Coprime (24*d) := by
  classical
  by_cases h : ∀ p : ℕ,p.Prime→p∣d→3<p
  · exact (goldbach_lower_residue_properties d h).2.2.2
  · simp [goldbachLowerSieveResidue,h]

noncomputable def goldbachLowerMainTerm (ψ : 𝓢(ℝ,ℝ)) (N : ℕ) (R : ℝ) (n : ℕ) : ℝ :=
  (goldbachArithmeticFactor R 24 1 11 n/((24:ℕ).totient:ℂ)*
    goldbachSingularIntegral ψ N 1 R (n:ℝ) (N:ℝ) ((N:ℝ)^2)).re

theorem goldbach_lower_base_real_positive (R : ℝ) (hR : 3≤R) (n : ℤ)
    (hn : (n:ZMod 24)=12) :
    0<(goldbachArithmeticFactor R 24 1 11 n).re ∧
      (goldbachArithmeticFactor R 24 1 11 n).im=0 := by
  classical
  let v : ℝ := 24*∏ p∈goldbachLargeLocalPrimes R,
    (p:ℝ)*((p:ℝ)-1-(goldbachRho p n:ℝ))/((p:ℝ)-1)^2
  have hv : 0<v := by
    apply mul_pos (by norm_num)
    apply prod_pos
    intro p hp
    obtain ⟨hprime,hlarge,_⟩ := (mem_goldbach_large_local_primes (by linarith) p).mp hp
    have : Fact p.Prime := ⟨hprime⟩
    have hp' : (3:ℝ)<p := by exact_mod_cast hlarge
    exact div_pos (mul_pos (by linarith) (goldbach_local_denominator_pos p hlarge n))
      (sq_pos_of_pos (by linarith))
  have hphase : ((n-(1:ℤ)*11:ℤ):ZMod 24)=1 := by
    norm_num [Int.cast_sub,Int.cast_mul,hn]
  have he : goldbachArithmeticFactor R 24 1 11 n=(v:ℂ) := by
    have hlarge := goldbach_arithmetic_factor_large_primes R hR 24 1 (by decide) 11 n (by decide) hphase
    simp only [Nat.cast_one] at hlarge
    rw [hlarge]
    dsimp only [v]
    push_cast
    congr 1
    apply prod_congr rfl
    intro p hp
    obtain ⟨hprime,hlarge,_⟩ := (mem_goldbach_large_local_primes (by linarith) p).mp hp
    have : Fact p.Prime := ⟨hprime⟩
    exact goldbach_prime_unrestricted_factor p 24
      (goldbach_large_prime_coprime_twentyfour p hprime hlarge) 1 11 n (by simp)
  rw [he]
  exact ⟨hv,rfl⟩

theorem goldbach_lower_main_term_nonneg (ψ : 𝓢(ℝ,ℝ)) (hψ : ψ≠0)
    (N : ℕ) (hN : 2≤N) (R : ℝ) (hR : 3≤R) (n : ℕ)
    (hn : (n:ZMod 24)=12) : 0≤goldbachLowerMainTerm ψ N R n := by
  have hG := goldbach_lower_base_real_positive R hR (n:ℤ) (by simpa only [Int.cast_natCast] using hn)
  have hNr : (2:ℝ)≤N := by exact_mod_cast hN
  have hH := goldbach_singular_integral_nonnegative ψ hψ N 1 (by omega) (by decide)
    (by linarith : 0<R) hNr (by nlinarith : (2:ℝ)≤(N:ℝ)^2) (n:ℝ)
  unfold goldbachLowerMainTerm
  rw [show Nat.totient 24=8 by decide]
  have hG0 := hG.1.le
  have hH0 := hH.1
  norm_num [Complex.div_re,Complex.mul_re,hG.2,hH.2]
  positivity

theorem goldbach_lower_divisor_real_identity (ψ : 𝓢(ℝ,ℝ)) (N n d : ℕ)
    (R : ℝ) (hR : 3≤R) (hn : (n:ZMod 24)=12) (hd : Squarefree d)
    (hs : ∀ p∈d.primeFactors,3<p) :
    goldbachSequenceDivisorCount (goldbachAdmissibleRepresentations n) (fun r=>r-1) d=
      goldbachLowerMainTerm ψ N R n*goldbachPrimeDensityProduct (goldbachLowerDensity R n) d+
        (goldbachFullRemainder ψ N 1 (24*d) (goldbachLowerSieveResidue d) R n).re := by
  classical
  have hsup : ∀ p : ℕ,p.Prime→p∣d→3<p := fun p hp hpd=>hs p (hp.mem_primeFactors hpd hd.ne_zero)
  obtain ⟨_,ha24,had,hac⟩ := goldbach_lower_residue_properties d hsup
  have hc := goldbach_lower_sequence_circle_identity ψ N n d (goldbachLowerSieveResidue d)
    (goldbach_sieve_support_coprime_six d hsup) ha24 had R
  have hf := goldbach_lower_density_factorization R hR d hd hs
    (goldbachLowerSieveResidue d:ℤ) (n:ℤ) hac.symm.isCoprime
    (by simpa only [Int.cast_natCast,Nat.cast_ofNat] using
      (ZMod.natCast_eq_natCast_iff _ _ 24).mpr ha24)
    (by simpa only [Int.cast_natCast,Nat.cast_one] using
      (ZMod.natCast_eq_natCast_iff _ _ d).mpr had)
    (by simpa only [Int.cast_natCast] using hn)
  rw [hf,goldbach_sieve_omega_div _ d hd.ne_zero] at hc
  have hc' : ((goldbachLowerDivisibilityValues n d).card:ℂ)=
      (goldbachArithmeticFactor R 24 1 11 n/((24:ℕ).totient:ℂ)*
        goldbachSingularIntegral ψ N 1 R (n:ℝ) (N:ℝ) ((N:ℝ)^2))*
          (goldbachPrimeDensityProduct (goldbachLowerDensity R n) d:ℂ)+
        goldbachFullRemainder ψ N 1 (24*d) (goldbachLowerSieveResidue d) R n := by
    dsimp only [goldbachPrimeDensityProduct]
    convert hc using 1; ring
  have hr := congrArg Complex.re hc'
  rw [goldbach_lower_divisibility_values_card] at hr
  simpa only [goldbachSequenceDivisorCount,goldbachLowerDivisibilitySequence,
    goldbachLowerMainTerm,goldbachPrimeDensityProduct,Complex.add_re,Complex.natCast_re,
    Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero] using hr

theorem goldbach_lower_sifted_sequence (n : ℕ) (z : ℝ) :
    goldbachSequenceSiftedCount (goldbachAdmissibleRepresentations n) (fun r=>r-1)
      (goldbachLowerSievePrimes z)=((goldbachFixedLowerSiftedValues n z).card:ℝ) := by
  classical
  have hfilter : (goldbachAdmissibleRepresentations n).filter
      (fun r=>∀ p∈goldbachLowerSievePrimes z,¬p∣r-1)=goldbachFixedLowerSifted n z := by
    ext r
    simp only [goldbachFixedLowerSifted,mem_filter]
    constructor
    · rintro ⟨hr,hp⟩
      exact ⟨hr,fun p hs hz=>hp p ((mem_goldbach_lower_sieve_primes z p).mpr ⟨hs,hz⟩)⟩
    · rintro ⟨hr,hp⟩
      exact ⟨hr,fun p hs=>hp p ((mem_goldbach_lower_sieve_primes z p).mp hs).1
        ((mem_goldbach_lower_sieve_primes z p).mp hs).2⟩
  have hcard : (goldbachFixedLowerSiftedValues n z).card=(goldbachFixedLowerSifted n z).card := by
    apply card_image_iff.mpr
    intro r hr t ht he
    have hrp := (mem_goldbachRepresentations.mp (mem_filter.mp (mem_filter.mp hr).1).1).1.two_le
    have htp := (mem_goldbachRepresentations.mp (mem_filter.mp (mem_filter.mp ht).1).1).1.two_le
    change r-1=t-1 at he
    omega
  simp only [goldbachSequenceSiftedCount,hfilter,hcard]

end PrimeSquares

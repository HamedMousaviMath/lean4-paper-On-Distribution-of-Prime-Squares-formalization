import PrimeSquares.GoldbachUpperSieveDensity
import PrimeSquares.GoldbachUpperSieveSequence
import PrimeSquares.GoldbachPositiveSingularComplete

set_option autoImplicit false
open Finset
namespace PrimeSquares

noncomputable def goldbachUpperSieveResidue (ℓ d : ℕ) : ℕ := by
  classical
  exact if h : (ℓ/2).Coprime 6 ∧ ℓ=2*(ℓ/2) ∧ 0<d ∧ d.Coprime (12*ℓ) then
    Classical.choose (goldbach_upper_sieve_residue (ℓ/2) d h.1 h.2.2.1 (by rw [←h.2.1];exact h.2.2.2))
    else 1

theorem goldbach_upper_residue_properties (v d : ℕ) (hv : v.Coprime 6)
    (hd : 0<d) (hdc : d.Coprime (12*(2*v))) :
    goldbachUpperSieveResidue (2*v) d<12*d ∧
      Nat.ModEq 12 (v*goldbachUpperSieveResidue (2*v) d) 5 ∧
      Nat.ModEq d ((2*v)*goldbachUpperSieveResidue (2*v) d+1) 0 ∧
      (goldbachUpperSieveResidue (2*v) d).Coprime (12*d) := by
  classical
  have he : 2*v/2=v := by omega
  have hh : (2*v/2).Coprime 6 ∧ 2*v=2*(2*v/2) ∧ 0<d ∧ d.Coprime (12*(2*v)) := by
    rw [he];exact ⟨hv,rfl,hd,hdc⟩
  rw [goldbachUpperSieveResidue,dite_eq_left hh]
  simpa only [he] using Classical.choose_spec
    (goldbach_upper_sieve_residue (2*v/2) d hh.1 hh.2.2.1 (by rw [←hh.2.1];exact hh.2.2.2))

theorem goldbach_upper_residue_coprime (ℓ d : ℕ) :
    (goldbachUpperSieveResidue ℓ d).Coprime (12*d) := by
  classical
  by_cases h : (ℓ/2).Coprime 6 ∧ ℓ=2*(ℓ/2) ∧ 0<d ∧ d.Coprime (12*ℓ)
  · have hh := (goldbach_upper_residue_properties (ℓ/2) d h.1 h.2.2.1 (by rw [←h.2.1];exact h.2.2.2)).2.2.2
    simpa only [←h.2.1] using hh
  · simp only [goldbachUpperSieveResidue,dite_eq_right h]
    exact Nat.coprime_one_left _

theorem goldbach_upper_main_term_nonneg (ψ : SchwartzMap ℝ ℝ) (hψ : ψ≠0)
    (N : ℕ) (hN : 2≤N) (R : ℝ) (hR : 3≤R) (v n : ℕ) (hv : v.Coprime 6)
    (hn : (n:ZMod 24)=12) : 0≤goldbachUpperMainTerm ψ N R (2*v) n := by
  have hv0 : 0<v := by
    by_contra h
    have he : v=0 := by omega
    subst v
    norm_num at hv
  have hG := goldbach_upper_arithmetic_real_product R hR v hv (n:ℤ)
    (by simpa only [Int.cast_natCast] using hn)
  have hNr : (2:ℝ)≤N := by exact_mod_cast hN
  have hH := goldbach_singular_integral_nonnegative ψ hψ N (2*v) (by omega)
    (by positivity) (by linarith : 0<R) hNr (by nlinarith : (2:ℝ)≤(N:ℝ)^2) ((n:ℝ)-1)
  have hprod : 0≤24*∏ p∈goldbachLargeLocalPrimes R,goldbachUpperArithmeticReal p (2*v) n := by
    apply mul_nonneg (by norm_num)
    apply prod_nonneg
    intro p hp
    obtain ⟨hprime,hlarge,_⟩ := (mem_goldbach_large_local_primes (by linarith) p).mp hp
    exact goldbach_upper_arithmetic_real_nonneg hprime hlarge (2*v) n
  unfold goldbachUpperMainTerm
  rw [hG,show Nat.totient 12=4 by decide]
  norm_num only [Nat.cast_ofNat]
  have hden : ((2*v:ℕ):ℂ)*(4:ℂ)=((((2*v:ℕ):ℝ)*4:ℝ):ℂ) := by push_cast;ring
  rw [hden,←Complex.ofReal_div]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  exact mul_nonneg (div_nonneg hprod (by positivity)) hH.1

theorem goldbach_upper_divisor_real_identity (ψ : SchwartzMap ℝ ℝ) (N n v d : ℕ)
    (_hN : 2≤N) (hn : 0<n) (hnN : n<N^2) (hn24 : n%24=12)
    (hv : v.Coprime 6) (hv4 : v%4=3) (R : ℝ) (hR : 3≤R)
    (hd : Squarefree d) (hdc : d.Coprime (12*(2*v))) :
    goldbachSequenceDivisorCount (goldbachUpperM n N (2*v)) id d=
      goldbachUpperMainTerm ψ N R (2*v) n*
        goldbachPrimeDensityProduct (goldbachUpperDensity R n) d+
        (goldbachFullRemainder ψ N (2*v) (12*d) (goldbachUpperSieveResidue (2*v) d) R (n-1)).re := by
  classical
  obtain ⟨_,ha12,had,hac⟩ := goldbach_upper_residue_properties v d hv (Nat.pos_of_ne_zero hd.ne_zero) hdc
  have hc := goldbach_upper_sequence_circle_identity ψ N n v d (goldbachUpperSieveResidue (2*v) d)
    hn hnN hn24 hv hv4 hdc ha12 had R
  obtain ⟨hb,hvb⟩ := goldbach_upper_base_residue v hv
  have hnZ : ((n:ℤ):ZMod 24)=12 := by
    simpa only [Int.cast_natCast,Nat.cast_ofNat] using (ZMod.natCast_eq_natCast_iff n 12 24).mpr hn24
  have hf := goldbach_upper_density_factorization R hR v d hv hd hdc
    (goldbachUpperSieveResidue (2*v) d:ℤ) (goldbachUpperBaseResidue (2*v):ℤ) (n:ℤ)
    hac.symm.isCoprime hb.symm.isCoprime
    (by simpa only [Int.cast_natCast,Nat.cast_mul,Nat.cast_ofNat] using
      (ZMod.natCast_eq_natCast_iff (v*goldbachUpperSieveResidue (2*v) d) 5 12).mpr ha12)
    (by simpa only [Int.cast_natCast] using hvb)
    (by simpa only [Int.cast_add,Int.cast_mul,Int.cast_natCast,Int.cast_one,Int.cast_ofNat,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_add,Nat.cast_one,Nat.cast_zero] using
      (ZMod.natCast_eq_natCast_iff ((2*v)*goldbachUpperSieveResidue (2*v) d+1) 0 d).mpr had) hnZ
  have hnInt : ((n-1:ℕ):ℤ)=(n:ℤ)-1 := by omega
  have hnReal : ((n-1:ℕ):ℝ)=(n:ℝ)-1 := by exact_mod_cast hnInt
  rw [hnInt,hnReal] at hc
  have hrewrite : goldbachArithmeticFactor R (12*d) ((2*v:ℕ):ℤ)
      (goldbachUpperSieveResidue (2*v) d:ℤ) ((n:ℤ)-1)/
        (((2*v:ℕ):ℂ)*((12*d).totient:ℂ))=
      (goldbachArithmeticFactor R 12 ((2*v:ℕ):ℤ) (goldbachUpperBaseResidue (2*v):ℤ) ((n:ℤ)-1)/
        (((2*v:ℕ):ℂ)*((12:ℕ).totient:ℂ)))*
          (goldbachPrimeDensityProduct (goldbachUpperDensity R n) d:ℂ) := by
    rw [goldbach_sieve_omega_div _ d hd.ne_zero] at hf
    calc
      _=(goldbachArithmeticFactor R (12*d) ((2*v:ℕ):ℤ)
        (goldbachUpperSieveResidue (2*v) d:ℤ) ((n:ℤ)-1)/((12*d).totient:ℂ))/((2*v:ℕ):ℂ) := by ring
      _=_ := by rw [hf];dsimp only [goldbachPrimeDensityProduct];ring
  rw [hrewrite] at hc
  have hr := congrArg Complex.re hc
  simp only [goldbachUpperDivisibilitySequence,goldbachSequenceDivisorCount,id_eq,
    Complex.add_re,Complex.natCast_re] at hr ⊢
  rw [show (goldbachArithmeticFactor R 12 ((2*v:ℕ):ℤ) (goldbachUpperBaseResidue (2*v):ℤ) ((n:ℤ)-1)/
    (((2*v:ℕ):ℂ)*((12:ℕ).totient:ℂ)))*
      (goldbachPrimeDensityProduct (goldbachUpperDensity R n) d:ℂ)*
      goldbachSingularIntegral ψ N (2*v) R ((n:ℝ)-1) (N:ℝ) ((N:ℝ)^2)=
    (goldbachArithmeticFactor R 12 ((2*v:ℕ):ℤ) (goldbachUpperBaseResidue (2*v):ℤ) ((n:ℤ)-1)/
    (((2*v:ℕ):ℂ)*((12:ℕ).totient:ℂ))*
      goldbachSingularIntegral ψ N (2*v) R ((n:ℝ)-1) (N:ℝ) ((N:ℝ)^2))*
      (goldbachPrimeDensityProduct (goldbachUpperDensity R n) d:ℂ) by ring] at hr
  simpa only [goldbachUpperMainTerm,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    mul_zero,sub_zero] using hr

end PrimeSquares

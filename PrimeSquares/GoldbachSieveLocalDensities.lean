import PrimeSquares.GoldbachSieveDensityFactorization
import PrimeSquares.GoldbachLowerSieveSequence

set_option autoImplicit false
open Finset
namespace PrimeSquares

theorem goldbach_large_prime_coprime_twentyfour (p : ℕ) (hp : p.Prime) (hlarge : 3 < p) :
    p.Coprime 24 := by
  have h2 : p.Coprime 2 := (Nat.coprime_primes hp (by decide)).mpr (by omega)
  have h3 : p.Coprime 3 := (Nat.coprime_primes hp (by decide)).mpr (by omega)
  simpa only [show (2:ℕ)^3*3=24 by decide] using (h2.pow_right 3).mul_right h3

theorem goldbach_lower_base_nonzero (R : ℝ) (hR : 3≤R) (n : ℤ)
    (hn : (n:ZMod 24)=12) : goldbachArithmeticFactor R 24 1 11 n≠0 := by
  have hb : IsCoprime (24:ℤ) 11 := by decide
  have hphase : ((n-(1:ℤ)*11:ℤ):ZMod 24)=1 := by
    norm_num [Int.cast_sub,Int.cast_mul,hn]
  have he := goldbach_arithmetic_factor_large_primes R hR 24 1 (by decide) 11 n hb hphase
  simp only [Nat.cast_one] at he
  rw [he]
  apply mul_ne_zero (by norm_num)
  apply prod_ne_zero_iff.mpr
  intro p hp
  obtain ⟨hprime,hlarge,_⟩ := (mem_goldbach_large_local_primes (by linarith) p).mp hp
  have : Fact p.Prime := ⟨hprime⟩
  rw [goldbach_prime_unrestricted_factor p 24
    (goldbach_large_prime_coprime_twentyfour p hprime hlarge) 1 11 n (by simp)]
  apply div_ne_zero
  · apply mul_ne_zero (by exact_mod_cast hprime.ne_zero)
    exact_mod_cast (goldbach_local_denominator_pos p hlarge n).ne'
  · exact pow_ne_zero 2 (sub_ne_zero.mpr (by exact_mod_cast hprime.ne_one))

theorem goldbach_lower_density_factorization (R : ℝ) (hR : 3≤R) (d : ℕ)
    (hd : Squarefree d) (hS : ∀ p∈d.primeFactors,3 < p)
    (b n : ℤ) (hb : IsCoprime ((24*d:ℕ):ℤ) b)
    (hb24 : (b:ZMod 24)=11) (hbd : (b:ZMod d)=1) (hn : (n:ZMod 24)=12) :
    goldbachArithmeticFactor R (24*d) 1 b n/((24*d).totient:ℂ)=
      goldbachArithmeticFactor R 24 1 11 n/((24:ℕ).totient:ℂ)*
        ((goldbachSieveOmega (goldbachLowerDensity R n) d/(d:ℝ):ℝ):ℂ) := by
  have h6 : d.Coprime 6 := goldbach_sieve_support_coprime_six d (by
    intro p hp hpd
    exact hS p (hp.mem_primeFactors hpd hd.ne_zero))
  have hKd := goldbach_sieve_coprime_twentyfour h6
  have hphase : ((n-(1:ℤ)*b:ℤ):ZMod 24)=1 := by
    norm_num [Int.cast_sub,Int.cast_mul,hn,hb24]
  have hS' : ∀ p∈d.primeFactors,3 < p ∧ IsUnit ((1:ℤ):ZMod p) ∧
      ((1:ℤ):ZMod p)*(b:ZMod p)=((1:ℤ):ZMod p) := by
    intro p hp
    have hbp := congrArg (ZMod.castHom (Nat.dvd_of_mem_primeFactors hp) (ZMod p)) hbd
    simp only [map_intCast,map_one] at hbp
    exact ⟨hS p hp,by simp,by simpa only [Int.cast_one,one_mul] using hbp⟩
  have h := goldbach_sieve_density_factorization R hR 24 1 d hd hKd (by decide) b n 1 hphase hS' hb
  simp only [Nat.cast_one] at h
  have hb₀ : IsCoprime (24:ℤ) b := integer_coprime_of_nat_dvd 24 (24*d) b hb (dvd_mul_right 24 d)
  rw [goldbach_arithmetic_factor_residue_congr R 24 1 b 11 n hb₀ (by decide)
    (by simpa only [Int.cast_ofNat] using hb24)] at h
  exact h

theorem goldbach_lower_local_density_formula (R : ℝ) (hR : 3≤R) (p : ℕ) [Fact p.Prime]
    (hp : 3 < p) (b n : ℤ) (hb : IsCoprime ((24*p:ℕ):ℤ) b)
    (hb24 : (b:ZMod 24)=11) (hbp : (b:ZMod p)=1) (hn : (n:ZMod 24)=12) :
    ((24:ℕ).totient:ℂ)*goldbachArithmeticFactor R (24*p) 1 b n/
      (((24*p).totient:ℂ)*goldbachArithmeticFactor R 24 1 11 n)=
        (goldbachLowerDensity R n p:ℂ) := by
  have hprime : p.Prime := Fact.out
  have h := goldbach_lower_density_factorization R hR p hprime.squarefree
    (by intro q hq;rw [hprime.primeFactors,mem_singleton] at hq;simpa only [hq] using hp)
    b n hb hb24 hbp hn
  rw [goldbach_sieve_omega_prime _ p hprime] at h
  have hφ : ((24*p).totient:ℂ)≠0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.mul_pos (by decide) hprime.pos)).ne'
  have hφ24 : ((24:ℕ).totient:ℂ)≠0 := by norm_num [show Nat.totient 24=8 by decide]
  have hG := goldbach_lower_base_nonzero R hR n hn
  field_simp at h ⊢
  linear_combination h

theorem goldbach_upper_phase_twentyfour (v : ℕ) (b n : ℤ)
    (hb : (v:ZMod 12)*(b:ZMod 12)=5) (hn : (n:ZMod 24)=12) :
    (((n-1)-((2*v:ℕ):ℤ)*b:ℤ):ZMod 24)=1 := by
  have hb' : ZMod.castHom (by decide : 12∣24) (ZMod 12)
      ((((v:ℤ)*b:ℤ):ZMod 24))=((5:ℤ):ZMod 12) := by
    simpa only [map_intCast,map_mul,map_natCast,Int.cast_mul,Int.cast_natCast,Int.cast_ofNat] using hb
  have h := goldbach_modular_multiplier_constant 24 12 2 (by decide) (by decide) 5
    ((((v:ℤ)*b:ℤ):ZMod 24)) hb'
  have he : (((2*v:ℕ):ℤ):ZMod 24)*(b:ZMod 24)=10 := by
    calc
      _=(2:ZMod 24)*((((v:ℤ)*b:ℤ):ZMod 24)) := by push_cast;ring
      _=(2:ZMod 24)*(5:ZMod 24) := h
      _=10 := by norm_num
  push_cast at he ⊢
  rw [hn,he]
  norm_num

theorem goldbach_upper_density_factorization (R : ℝ) (hR : 3≤R) (v d : ℕ)
    (hv : v.Coprime 6) (hd : Squarefree d) (hdc : d.Coprime (12*(2*v)))
    (b a n : ℤ) (hb : IsCoprime ((12*d:ℕ):ℤ) b) (ha : IsCoprime (12:ℤ) a)
    (hvb : (v:ZMod 12)*(b:ZMod 12)=5) (hva : (v:ZMod 12)*(a:ZMod 12)=5)
    (hbd : ((((2*v:ℕ):ℤ)*b+1:ℤ):ZMod d)=0) (hn : (n:ZMod 24)=12) :
    goldbachArithmeticFactor R (12*d) ((2*v:ℕ):ℤ) b (n-1)/((12*d).totient:ℂ)=
      goldbachArithmeticFactor R 12 ((2*v:ℕ):ℤ) a (n-1)/((12:ℕ).totient:ℂ)*
        ((goldbachSieveOmega (goldbachUpperDensity R n) d/(d:ℝ):ℝ):ℂ) := by
  have hKd : (12:ℕ).Coprime d :=
    (Nat.Coprime.of_dvd_right (dvd_mul_right 12 (2*v)) hdc).symm
  have h24 : 24∣(2*v)*12 := ⟨v,by ring⟩
  have hphase := goldbach_upper_phase_twentyfour v b n hvb hn
  have hS : ∀ p∈d.primeFactors,3 < p ∧ IsUnit (((2*v:ℕ):ℤ):ZMod p) ∧
      (((2*v:ℕ):ℤ):ZMod p)*(b:ZMod p)=((-1:ℤ):ZMod p) := by
    intro p hp
    have hprime := Nat.prime_of_mem_primeFactors hp
    have hpd := Nat.dvd_of_mem_primeFactors hp
    have hc : p.Coprime (12*(2*v)) := Nat.Coprime.of_dvd_left hpd hdc
    have hc12 : p.Coprime 12 := Nat.Coprime.of_dvd_right (dvd_mul_right 12 (2*v)) hc
    have hnot : ¬p∣12 := (hprime.coprime_iff_not_dvd).mp hc12
    have hlarge : 3 < p := by
      by_contra! h
      have hh : p=2 ∨ p=3 := by have := hprime.two_le;omega
      rcases hh with h|h <;> apply hnot <;> rw [h] <;> decide
    have hcℓ : p.Coprime (2*v) := Nat.Coprime.of_dvd_right (dvd_mul_left (2*v) 12) hc
    have hu : IsUnit (((2*v:ℕ):ℤ):ZMod p) := by
      simpa only [Int.cast_natCast] using (ZMod.isUnit_iff_coprime (2*v) p).mpr hcℓ.symm
    have hh := congrArg (ZMod.castHom hpd (ZMod p)) hbd
    simp only [map_intCast,map_zero] at hh
    push_cast at hh
    refine ⟨hlarge,hu,?_⟩
    push_cast
    exact eq_neg_iff_add_eq_zero.mpr hh
  have h := goldbach_sieve_density_factorization R hR 12 (2*v) d hd hKd h24 b (n-1) (-1) hphase hS hb
  have ht : (n-1)-(-1)=n := by ring
  rw [ht] at h
  have hv12 : v.Coprime 12 := Nat.Coprime.of_dvd_right (by decide : 12∣24)
    (goldbach_sieve_coprime_twentyfour hv).symm
  have hunit : IsUnit (v:ZMod 12) := (ZMod.isUnit_iff_coprime v 12).mpr hv12
  have hba : (b:ZMod 12)=(a:ZMod 12) := (IsUnit.mul_right_inj hunit).mp (hvb.trans hva.symm)
  have hb₀ : IsCoprime (12:ℤ) b := integer_coprime_of_nat_dvd 12 (12*d) b hb (dvd_mul_right 12 d)
  rw [goldbach_arithmetic_factor_residue_congr R 12 ((2*v:ℕ):ℤ) b a (n-1) hb₀ ha hba] at h
  exact h

theorem goldbach_upper_local_density (R : ℝ) (hR : 3≤R) (v : ℕ)
    (hv : v.Coprime 6) (n : ℤ) (hn : (n:ZMod 24)=12) :
    ∃ ω : ℕ→ℝ,ω 1=1 ∧
      (∀ d e : ℕ,d.Coprime e→ω (d*e)=ω d*ω e) ∧
      (∀ p : ℕ,p.Prime→¬p∣12*(2*v)→
        ω p/(p:ℝ)=goldbachUpperDensity R n p ∧ 0≤ω p/(p:ℝ) ∧ ω p/(p:ℝ) < 1) ∧
      (∀ d : ℕ,Squarefree d→d.Coprime (12*(2*v))→
        ∀ b a : ℤ,IsCoprime ((12*d:ℕ):ℤ) b→IsCoprime (12:ℤ) a→
          (v:ZMod 12)*(b:ZMod 12)=5→(v:ZMod 12)*(a:ZMod 12)=5→
          ((((2*v:ℕ):ℤ)*b+1:ℤ):ZMod d)=0→
          goldbachArithmeticFactor R (12*d) ((2*v:ℕ):ℤ) b (n-1)/((12*d).totient:ℂ)=
            goldbachArithmeticFactor R 12 ((2*v:ℕ):ℤ) a (n-1)/((12:ℕ).totient:ℂ)*
              ((ω d/(d:ℝ):ℝ):ℂ)) := by
  refine ⟨goldbachSieveOmega (goldbachUpperDensity R n),goldbach_sieve_omega_one _,?_,?_,?_⟩
  · exact goldbach_sieve_omega_mul _
  · intro p hp hnot
    have : Fact p.Prime := ⟨hp⟩
    have hnot12 : ¬p∣12 := fun h=>hnot (h.mul_right (2*v))
    have hlarge : 3 < p := by
      by_contra! h
      have hh : p=2 ∨ p=3 := by have := hp.two_le;omega
      rcases hh with h|h <;> apply hnot12 <;> rw [h] <;> decide
    rw [goldbach_sieve_omega_prime _ p hp]
    exact ⟨rfl,goldbach_upper_density_range R p hlarge n⟩
  · intro d hd hdc b a hb ha hvb hva hbd
    exact goldbach_upper_density_factorization R hR v d hv hd hdc b a n hb ha hvb hva hbd hn

end PrimeSquares

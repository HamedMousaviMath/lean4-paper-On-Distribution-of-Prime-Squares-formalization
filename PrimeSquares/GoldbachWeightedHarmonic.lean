import PrimeSquares.GoldbachWeightedMeanInputs
import PrimeSquares.GoldbachRankinLocal

set_option autoImplicit false
open Finset
namespace PrimeSquares

theorem goldbach_weighted_prime_harmonic_local (R : ℝ) (n : ℤ) (p J : ℕ) (hp : p.Prime) :
    (∑ j∈range (J+1),goldbachWeightedMultiplicative R n (p^j)/(p^j:ℕ))≤
      1+goldbachWeightedPrimeValue R n p/((p:ℝ)-1) := by
  have hpR : (1:ℝ)<p := by exact_mod_cast hp.one_lt
  have ht0 : (0:ℝ)≤(p:ℝ)⁻¹ := inv_nonneg.mpr (by linarith)
  have ht1 : (p:ℝ)⁻¹<1 := (inv_lt_one₀ (by linarith : (0:ℝ)<p)).mpr hpR
  rw [sum_range_succ']
  simp only [pow_zero,goldbach_weighted_multiplicative_one,Nat.cast_one,div_one]
  have hs : (∑ j∈range J,goldbachWeightedMultiplicative R n (p^(j+1))/(p^(j+1):ℕ))=
      (goldbachWeightedPrimeValue R n p/(p:ℝ))*(∑ j∈range J,((p:ℝ)⁻¹)^j) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro j _
    rw [goldbach_weighted_prime_power R n p j hp,Nat.cast_pow,pow_succ]
    simp only [inv_pow,div_eq_mul_inv,mul_inv_rev]
    ring
  rw [hs]
  have hh := mul_le_mul_of_nonneg_left (goldbach_geometric_partial_bound ht0 ht1 J)
    (div_nonneg (goldbach_weighted_prime_nonneg R n hp) (by linarith : (0:ℝ)≤p))
  have he : (goldbachWeightedPrimeValue R n p/(p:ℝ))*(1/(1-(p:ℝ)⁻¹))=
      goldbachWeightedPrimeValue R n p/((p:ℝ)-1) := by
    field_simp [show (p:ℝ)≠0 by linarith,show (p:ℝ)-1≠0 by linarith]
  rw [he] at hh
  linarith

theorem goldbach_weighted_harmonic_divisors (R : ℝ) (n : ℤ) (D : ℕ) (hD : D≠0) :
    (∑ u∈D.divisors,goldbachWeightedMultiplicative R n u/(u:ℝ))≤
      ∏ p∈D.primeFactors,(1+goldbachWeightedPrimeValue R n p/((p:ℝ)-1)) := by
  have he := sum_divisors_multiplicative
    (fun u : ℕ=>goldbachWeightedMultiplicative R n u/(u:ℝ))
    (by simp only [goldbachWeightedMultiplicative,ite_true,Nat.cast_zero,div_zero])
    (by simp only [goldbach_weighted_multiplicative_one,Nat.cast_one,div_one])
    (fun a b hc=>by rw [goldbach_weighted_multiplicative_mul R n a b hc,Nat.cast_mul,mul_div_mul_comm]) D hD
  rw [he]
  apply prod_le_prod₀
  · intro p hp
    exact sum_nonneg (fun j _=>div_nonneg (goldbach_weighted_multiplicative_nonneg R n _) (Nat.cast_nonneg _))
  · intro p hp
    exact goldbach_weighted_prime_harmonic_local R n p _ (Nat.prime_of_mem_primeFactors hp)

theorem goldbach_weighted_harmonic_local_majorant (R : ℝ) (n : ℤ) (p : ℕ)
    (hp : p.Prime) (hp7 : 7≤p) :
    1+goldbachWeightedPrimeValue R n p/((p:ℝ)-1)≤(1-2/((p:ℝ)-3))⁻¹^3 := by
  have hpR : (7:ℝ)≤p := by exact_mod_cast hp7
  let x := 2/((p:ℝ)-3)
  have hx0 : 0≤x := div_nonneg (by norm_num) (by linarith)
  have hx1 : x<1 := goldbach_density_bound_lt_one p hp7
  have hxden : 0<1-x := by linarith
  have hinv : 1+x≤(1-x)⁻¹ := by
    rw [←one_div]
    apply (le_div_iff₀ hxden).mpr
    nlinarith only [sq_nonneg x]
  have hcube := pow_le_pow_left₀ (show 0≤1+x by linarith) hinv 3
  have hl : 6/((p:ℝ)-1)≤3*x := by
    dsimp only [x]
    rw [←mul_div_assoc]
    norm_num
    exact div_le_div_of_nonneg_left (by norm_num : (0:ℝ)≤6)
      (by linarith : 0<(p:ℝ)-3) (by linarith : (p:ℝ)-3≤(p:ℝ)-1)
  have hw := div_le_div_of_nonneg_right (goldbach_weighted_prime_le_six R n hp)
    (by linarith : 0≤(p:ℝ)-1)
  have hx3 : 0≤x^3 := pow_nonneg hx0 3
  nlinarith only [hcube,hl,hw,hx3,sq_nonneg x]

theorem goldbach_weighted_harmonic_product (R : ℝ) (n : ℤ) (P : Finset ℕ)
    (hP : ∀ p∈P,p.Prime) (K U : ℝ) (_hK : 0≤K) (hU : 2≤U)
    (hPU : ∀ p∈P,(p:ℝ)≤U) (hM : GoldbachClassicalIntervalMertens K) :
    (∏ p∈P,(1+goldbachWeightedPrimeValue R n p/((p:ℝ)-1)))≤
      3*((1+K/Real.log 2)*(Real.log (U+1)/Real.log 2)^2)^3 := by
  classical
  let S := P.filter (fun p : ℕ=>7≤p)
  let f := fun p : ℕ=>1+goldbachWeightedPrimeValue R n p/((p:ℝ)-1)
  have hf (p : ℕ) (hp : p∈P) : 0≤f p := by
    have hp2 : (2:ℝ)≤p := by exact_mod_cast (hP p hp).two_le
    dsimp only [f]
    have := div_nonneg (goldbach_weighted_prime_nonneg R n (hP p hp)) (by linarith : 0≤(p:ℝ)-1)
    linarith
  have hS : S⊆P.erase 5 := by
    intro p hp
    obtain ⟨hp,hp7⟩ := mem_filter.mp hp
    exact mem_erase.mpr ⟨by omega,hp⟩
  have herase : (∏ p∈P.erase 5,f p)=∏ p∈S,f p := by
    symm
    apply prod_subset hS
    intro p hp hpS
    obtain ⟨hp5,hpP⟩ := mem_erase.mp hp
    have hp7 : ¬7≤p := by intro h;exact hpS (mem_filter.mpr ⟨hpP,h⟩)
    have hp2 := (hP p hpP).two_le
    have h4 : p%4≠1 := by omega
    simp only [f,goldbachWeightedPrimeValue,ite_eq_right h4,zero_div,add_zero]
  have hsmall : (∏ p∈P,f p)≤3*∏ p∈S,f p := by
    by_cases h5 : 5∈P
    · rw [←mul_prod_erase P f h5,herase]
      have hfive : f 5≤3 := by
        have hh := goldbach_weighted_prime_le_six R n (by decide : Nat.Prime 5)
        dsimp only [f]
        norm_num
        linarith
      exact mul_le_mul_of_nonneg_right hfive (prod_nonneg (fun p hp=>hf p (mem_filter.mp hp).1))
    · rw [←erase_eq_of_notMem h5,herase]
      have hn : 0≤∏ p∈S,f p := prod_nonneg (fun p hp=>hf p (mem_filter.mp hp).1)
      linarith
  have hprod : (∏ p∈S,f p)≤(∏ p∈S,(1-2/((p:ℝ)-3))⁻¹)^3 := by
    rw [←prod_pow]
    apply prod_le_prod₀
    · intro p hp
      exact hf p (mem_filter.mp hp).1
    · intro p hp
      exact goldbach_weighted_harmonic_local_majorant R n p (hP p (mem_filter.mp hp).1) (mem_filter.mp hp).2
  have hm := hM.preliminary 2 (U+1) S le_rfl (by linarith) (by
    intro p hp
    obtain ⟨hpP,hp7⟩ := mem_filter.mp hp
    exact ⟨hP p hpP,hp7,by exact_mod_cast (show 2≤p by omega),by linarith [hPU p hpP]⟩)
  rw [Real.rpow_two] at hm
  have hprod0 : 0≤∏ p∈S,(1-2/((p:ℝ)-3))⁻¹ := by
    apply prod_nonneg
    intro p hp
    exact inv_nonneg.mpr (sub_pos.mpr (goldbach_density_bound_lt_one p (mem_filter.mp hp).2)).le
  exact hsmall.trans (mul_le_mul_of_nonneg_left
    (hprod.trans (pow_le_pow_left₀ hprod0 hm 3)) (by norm_num : (0:ℝ)≤3))

theorem goldbach_weighted_harmonic_uniform (R : ℝ) (n : ℤ) (K U : ℝ)
    (hK : 0≤K) (hU : 2≤U) (hM : GoldbachClassicalIntervalMertens K) :
    (∑ u∈Icc 1 ⌊U⌋₊,goldbachWeightedMultiplicative R n u/(u:ℝ))≤
      3*((1+K/Real.log 2)*(Real.log (U+1)/Real.log 2)^2)^3 := by
  classical
  let D := (⌊U⌋₊).factorial
  have hD : D≠0 := Nat.factorial_ne_zero _
  have hsubset : Icc 1 ⌊U⌋₊⊆D.divisors := by
    intro u hu
    obtain ⟨hu1,huB⟩ := mem_Icc.mp hu
    exact Nat.mem_divisors.mpr ⟨Nat.dvd_factorial (by omega) huB,hD⟩
  have hs := sum_le_sum_of_subset_of_nonneg hsubset
    (fun u _ _=>div_nonneg (goldbach_weighted_multiplicative_nonneg R n u) (Nat.cast_nonneg u))
  apply hs.trans ((goldbach_weighted_harmonic_divisors R n D hD).trans _)
  apply goldbach_weighted_harmonic_product R n D.primeFactors
    (fun p hp=>Nat.prime_of_mem_primeFactors hp) K U hK hU _ hM
  intro p hp
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hpU : p≤⌊U⌋₊ := hprime.dvd_factorial.mp (Nat.dvd_of_mem_primeFactors hp)
  have hpUR : (p:ℝ)≤(⌊U⌋₊:ℕ) := by exact_mod_cast hpU
  exact hpUR.trans (Nat.floor_le (by linarith : 0≤U))

end PrimeSquares

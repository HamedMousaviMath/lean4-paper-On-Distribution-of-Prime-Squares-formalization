import PrimeSquares.GoldbachFixedSieveComparison

set_option autoImplicit false
open Finset
namespace PrimeSquares

theorem goldbach_uniform_divisor_card {ε : ℝ} (hε : 0<ε) :
    ∃ K : ℝ,0<K ∧ ∀ N m : ℕ,1≤N →m≤N^2 →
      (m.divisors.card:ℝ)≤K*(N:ℝ)^ε := by
  obtain ⟨K,hK,hDiv⟩ := divisors_card_rpow_le_rpow (by norm_num : (0:ℝ)<1) (by linarith : 0<ε/2)
  refine ⟨K,hK,?_⟩
  intro N m hN hm
  have hn : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  by_cases hz : m=0
  · subst m
    simp only [Nat.divisors_zero,card_empty,Nat.cast_zero]
    positivity
  · have hb : (m.divisors.card:ℝ)≤K*(m:ℝ)^(ε/2) := by
      simpa only [Real.rpow_one] using hDiv m (Nat.pos_of_ne_zero hz)
    calc
      _≤K*(m:ℝ)^(ε/2) := hb
      _≤K*((N:ℝ)^2)^(ε/2) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hm) (by positivity)) hK.le
      _=K*(N:ℝ)^ε := by
        rw [←Real.rpow_natCast,←Real.rpow_mul hn.le]
        congr 2
        ring

theorem goldbach_fixed_sieve_divisor_sum {ε : ℝ} (hε : 0<ε) :
    ∃ K : ℝ,0<K ∧ ∀ N n : ℕ,1≤N →0<n →n≤N^2 →
      (∑ p∈n.primeFactors,((n-p^2-1).divisors.card:ℝ))≤K*(N:ℝ)^ε := by
  obtain ⟨K₁,hK₁,hP⟩ := goldbach_prime_divisor_power_error (by linarith : 0<ε/2)
  obtain ⟨K₂,hK₂,hD⟩ := goldbach_uniform_divisor_card (by linarith : 0<ε/2)
  refine ⟨K₁*K₂,by positivity,?_⟩
  intro N n hN hn hsize
  have hPrime : (n.primeFactors.card:ℝ)≤K₁*(N:ℝ)^(ε/2) := by
    simpa only [Nat.add_sub_cancel] using hP N (n+1) hN (by omega) (by simpa only [Nat.add_sub_cancel] using hsize)
  have hnR : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  calc
    _≤∑ _p∈n.primeFactors,K₂*(N:ℝ)^(ε/2) := sum_le_sum (fun p _=>hD N (n-p^2-1) hN (by omega))
    _=(n.primeFactors.card:ℝ)*(K₂*(N:ℝ)^(ε/2)) := by rw [sum_const,nsmul_eq_mul]
    _≤(K₁*(N:ℝ)^(ε/2))*(K₂*(N:ℝ)^(ε/2)) := mul_le_mul_of_nonneg_right hPrime (by positivity)
    _=(K₁*K₂)*((N:ℝ)^(ε/2)*(N:ℝ)^(ε/2)) := by ring
    _=(K₁*K₂)*(N:ℝ)^ε := by rw [←Real.rpow_add hnR];congr 2;ring

theorem goldbach_fixed_sieve_sets {ε : ℝ} (hε : 0<ε) :
    ∃ K : ℝ,0<K ∧ ∀ N n : ℕ,1≤N →0<n →n≤N^2 →∀ z : ℝ,
      (goldbachFixedLowerSiftedValues n z).card≤(goldbachSiftedValues n z).card ∧
      (goldbachUpperSieveSum n N z:ℝ)≤(goldbachFixedUpperSieveSum n N z:ℝ)+K*(N:ℝ)^ε := by
  obtain ⟨K,hK,hError⟩ := goldbach_fixed_sieve_divisor_sum hε
  refine ⟨K,hK,?_⟩
  intro N n hN hn hsize z
  refine ⟨goldbach_fixed_lower_count n z,?_⟩
  have hh : (goldbachUpperSieveSum n N z:ℝ)≤(goldbachFixedUpperSieveSum n N z:ℝ)+
      ∑ p∈n.primeFactors,((n-p^2-1).divisors.card:ℝ) := by
    exact_mod_cast goldbach_fixed_upper_source_count_finite hn z
  exact hh.trans (add_le_add le_rfl (hError N n hN hn hsize))

end PrimeSquares

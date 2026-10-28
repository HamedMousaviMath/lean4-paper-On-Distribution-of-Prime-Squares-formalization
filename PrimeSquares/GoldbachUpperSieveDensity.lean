import PrimeSquares.GoldbachWeightedEulerProducts
import PrimeSquares.GoldbachLowerSieveDensity

set_option autoImplicit false
open Finset
namespace PrimeSquares

/-- Independent classical interval-product estimates for all primes.
The preliminary barrier includes the exceptional prime5 explicitly. -/
structure GoldbachClassicalFullIntervalMertens (K : ℝ) : Prop where
  preliminary : ∀ (w y : ℝ) (S : Finset ℕ),2≤w→w<y→
    (∀ p∈S,p.Prime ∧ 5≤p ∧ w≤(p:ℝ) ∧ (p:ℝ)<y)→
    (∏ p∈S,(1-(if p=5 then (1/2:ℝ) else 2/((p:ℝ)-3)))⁻¹)≤
      (1+K/Real.log w)*(Real.log y/Real.log w)^(2:ℝ)
  outer : ∀ (w y : ℝ) (S : Finset ℕ),2≤w→w<y→
    (∀ p∈S,p.Prime ∧ 5≤p ∧ w≤(p:ℝ) ∧ (p:ℝ)<y)→
    (∏ p∈S,(1-1/((p:ℝ)-1))⁻¹)≤
      (1+K/Real.log w)*(Real.log y/Real.log w)

noncomputable def goldbachUpperPreliminaryPrimes (ℓ : ℕ) (R z : ℝ) : Finset ℕ := by
  classical
  exact (goldbachUpperSievePrimes ℓ z).filter (fun p : ℕ=>(p:ℝ)≤R)

noncomputable def goldbachUpperOuterPrimes (ℓ : ℕ) (R z : ℝ) : Finset ℕ := by
  classical
  exact (goldbachUpperSievePrimes ℓ z).filter (fun p : ℕ=>R<(p:ℝ))

theorem goldbach_upper_sieve_prime_ge_five {ℓ p : ℕ} (hp : GoldbachFixedUpperSievePrime ℓ p) :
    5≤p := by
  have hlarge : 3<p := by
    by_contra! h
    have := hp.1.two_le
    have he : p=2 ∨ p=3 := by omega
    rcases he with he|he <;> apply hp.2 <;> rw [he] <;> omega
  have hne4 : p≠4 := by intro h;rw [h] at hp;exact (by decide : ¬Nat.Prime 4) hp.1
  omega

theorem goldbach_upper_prime_split (ℓ : ℕ) (R z : ℝ) :
    Disjoint (goldbachUpperPreliminaryPrimes ℓ R z) (goldbachUpperOuterPrimes ℓ R z) ∧
      goldbachUpperPreliminaryPrimes ℓ R z∪goldbachUpperOuterPrimes ℓ R z=
        goldbachUpperSievePrimes ℓ z := by
  classical
  constructor
  · apply disjoint_left.mpr
    intro p hp hq
    exact (not_lt_of_ge (mem_filter.mp hp).2) (mem_filter.mp hq).2
  · ext p
    simp only [goldbachUpperPreliminaryPrimes,goldbachUpperOuterPrimes,mem_union,mem_filter]
    by_cases hp : (p:ℝ)≤R
    · simp [hp,not_lt_of_ge hp]
    · simp [hp,lt_of_not_ge hp]

theorem goldbach_upper_density_multiplicative (ℓ : ℕ) (R z : ℝ) (n : ℤ) :
    GoldbachMultiplicativeDensityOn (goldbachUpperSievePrimes ℓ z)
      (goldbachPrimeDensityProduct (goldbachUpperDensity R n)) := by
  classical
  refine ⟨?_,?_,?_⟩
  · simp only [goldbachPrimeDensityProduct,Nat.primeFactors_one,prod_empty]
  · intro d e hd he hc _ _
    simp only [goldbachPrimeDensityProduct,Nat.primeFactors_mul hd.ne_zero he.ne_zero,
      prod_union hc.disjoint_primeFactors]
  · intro p hp
    have hs := ((mem_goldbach_upper_sieve_primes ℓ z p).mp hp).1
    have : Fact p.Prime := ⟨hs.1⟩
    simpa only [goldbachPrimeDensityProduct,hs.1.primeFactors,prod_singleton] using
      goldbach_upper_density_range R p (by have := goldbach_upper_sieve_prime_ge_five hs;omega) n

theorem goldbach_upper_preliminary_dimension (ℓ : ℕ) (K R z Z : ℝ)
    (hM : GoldbachClassicalFullIntervalMertens K) (n : ℤ) :
    GoldbachRefinedSieveDimension (goldbachUpperPreliminaryPrimes ℓ R z) Z 2 K
      (goldbachPrimeDensityProduct (goldbachUpperDensity R n)) := by
  classical
  intro w y hw hwy _
  let S := (goldbachUpperPreliminaryPrimes ℓ R z).filter
    (fun p : ℕ=>w≤(p:ℝ) ∧ (p:ℝ)<y)
  have hS : ∀ p∈S,p.Prime ∧ 5≤p ∧ w≤(p:ℝ) ∧ (p:ℝ)<y := by
    intro p hp
    obtain ⟨hp,hwin⟩ := mem_filter.mp hp
    have hs := ((mem_goldbach_upper_sieve_primes ℓ z p).mp (mem_filter.mp hp).1).1
    exact ⟨hs.1,goldbach_upper_sieve_prime_ge_five hs,hwin⟩
  have hprod : (∏ p∈S,(1-goldbachPrimeDensityProduct (goldbachUpperDensity R n) p)⁻¹)≤
      ∏ p∈S,(1-(if p=5 then (1/2:ℝ) else 2/((p:ℝ)-3)))⁻¹ := by
    apply prod_le_prod₀
    · intro p hp
      have hs := hS p hp
      have : Fact p.Prime := ⟨hs.1⟩
      rw [goldbachPrimeDensityProduct,hs.1.primeFactors,prod_singleton]
      exact inv_nonneg.mpr (sub_pos.mpr (goldbach_upper_density_range R p (by omega) n).2).le
    · intro p hp
      have hs := hS p hp
      have : Fact p.Prime := ⟨hs.1⟩
      rw [goldbachPrimeDensityProduct,hs.1.primeFactors,prod_singleton]
      have hb : goldbachUpperDensity R n p≤(if p=5 then (1/2:ℝ) else 2/((p:ℝ)-3)) := by
        by_cases he : p=5
        · subst p
          simp only [ite_true]
          exact goldbach_upper_density_five R n
        · rw [ite_eq_right he]
          exact goldbach_local_density_le R p (by omega) n (n-1)
      have hpos : 0<1-(if p=5 then (1/2:ℝ) else 2/((p:ℝ)-3)) := by
        by_cases he : p=5
        · norm_num [he]
        · rw [ite_eq_right he]
          exact sub_pos.mpr (goldbach_density_bound_lt_one p (by
            have h6 : p≠6 := by intro h;rw [h] at hs;exact (by decide : ¬Nat.Prime 6) hs.1
            omega))
      simpa only [one_div] using one_div_le_one_div_of_le hpos (sub_le_sub_left hb 1)
  exact hprod.trans (hM.preliminary w y S hw hwy hS)

theorem goldbach_upper_outer_dimension (ℓ : ℕ) (K R z : ℝ)
    (hM : GoldbachClassicalFullIntervalMertens K) (n : ℤ) :
    GoldbachRefinedSieveDimension (goldbachUpperOuterPrimes ℓ R z) z 1 K
      (goldbachPrimeDensityProduct (goldbachUpperDensity R n)) := by
  classical
  intro w y hw hwy _
  let S := (goldbachUpperOuterPrimes ℓ R z).filter
    (fun p : ℕ=>w≤(p:ℝ) ∧ (p:ℝ)<y)
  have hS : ∀ p∈S,p.Prime ∧ 5≤p ∧ w≤(p:ℝ) ∧ (p:ℝ)<y := by
    intro p hp
    obtain ⟨hp,hwin⟩ := mem_filter.mp hp
    have hs := ((mem_goldbach_upper_sieve_primes ℓ z p).mp (mem_filter.mp hp).1).1
    exact ⟨hs.1,goldbach_upper_sieve_prime_ge_five hs,hwin⟩
  have he : (∏ p∈S,(1-goldbachPrimeDensityProduct (goldbachUpperDensity R n) p)⁻¹)=
      ∏ p∈S,(1-1/((p:ℝ)-1))⁻¹ := by
    apply prod_congr rfl
    intro p hp
    have hs := hS p hp
    have hR := (mem_filter.mp (mem_filter.mp hp).1).2
    simp only [goldbachPrimeDensityProduct,hs.1.primeFactors,prod_singleton,
      goldbachUpperDensity,goldbachLocalDensity,ite_eq_right (not_le.mpr hR)]
  simpa only [Real.rpow_one] using he.trans_le (hM.outer w y S hw hwy hS)

end PrimeSquares

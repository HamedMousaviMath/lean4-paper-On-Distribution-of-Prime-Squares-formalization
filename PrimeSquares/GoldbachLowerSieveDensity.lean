import PrimeSquares.GoldbachPresieveClassicalInputs
import PrimeSquares.GoldbachSieveLocalDensities

set_option autoImplicit false
open Finset
namespace PrimeSquares

/- Independent interval-product versions of classical Mertens estimates.
   They contain no sequence, Goldbach main term, or sieve conclusion. -/
structure GoldbachClassicalIntervalMertens (K : ℝ) : Prop where
  preliminary : ∀ (w y : ℝ) (S : Finset ℕ),2≤w→w<y→
    (∀ p∈S,p.Prime ∧ 7≤p ∧ w≤(p:ℝ) ∧ (p:ℝ)<y)→
    (∏ p∈S,(1-2/((p:ℝ)-3))⁻¹)≤
      (1+K/Real.log w)*(Real.log y/Real.log w)^(2:ℝ)
  half : ∀ (w y : ℝ) (S : Finset ℕ),2≤w→w<y→
    (∀ p∈S,GoldbachFixedLowerSievePrime p ∧ w≤(p:ℝ) ∧ (p:ℝ)<y)→
    (∏ p∈S,(1-1/((p:ℝ)-1))⁻¹)≤
      (1+K/Real.log w)*(Real.log y/Real.log w)^((1:ℝ)/2)

noncomputable def goldbachLowerSievePrimes (z : ℝ) : Finset ℕ := by
  classical
  exact (range (Nat.ceil z)).filter GoldbachFixedLowerSievePrime

noncomputable def goldbachLowerPreliminaryPrimes (R z : ℝ) : Finset ℕ := by
  classical
  exact (goldbachLowerSievePrimes z).filter (fun p : ℕ=>(p:ℝ)≤R)

noncomputable def goldbachLowerOuterPrimes (R z : ℝ) : Finset ℕ := by
  classical
  exact (goldbachLowerSievePrimes z).filter (fun p : ℕ=>R<(p:ℝ))

theorem mem_goldbach_lower_sieve_primes (z : ℝ) (p : ℕ) :
    p∈goldbachLowerSievePrimes z ↔GoldbachFixedLowerSievePrime p ∧ (p:ℝ)<z := by
  classical
  simp only [goldbachLowerSievePrimes,mem_filter,mem_range,Nat.lt_ceil]
  exact and_comm

theorem goldbach_lower_prime_ge_seven {p : ℕ} (hp : GoldbachFixedLowerSievePrime p) :
    7≤p := by
  obtain ⟨_,hp,hr⟩ := hp
  omega

theorem goldbach_lower_prime_split (R z : ℝ) :
    Disjoint (goldbachLowerPreliminaryPrimes R z) (goldbachLowerOuterPrimes R z) ∧
      goldbachLowerPreliminaryPrimes R z∪goldbachLowerOuterPrimes R z=
        goldbachLowerSievePrimes z := by
  classical
  constructor
  · apply disjoint_left.mpr
    intro p hp hq
    exact (not_lt_of_ge (mem_filter.mp hp).2) (mem_filter.mp hq).2
  · ext p
    simp only [goldbachLowerPreliminaryPrimes,goldbachLowerOuterPrimes,mem_union,mem_filter]
    by_cases hp : (p:ℝ)≤R
    · simp [hp,not_lt_of_ge hp]
    · simp [hp,lt_of_not_ge hp]

theorem goldbach_lower_prime_density_range (R : ℝ) (n : ℤ) {p : ℕ}
    (hp : GoldbachFixedLowerSievePrime p) :
    0≤goldbachLowerDensity R n p ∧ goldbachLowerDensity R n p<1 := by
  have : Fact p.Prime := ⟨hp.1⟩
  exact ⟨goldbach_local_density_nonneg R p hp.2.1 (n-1) n,
    goldbach_local_density_lt_one R p (goldbach_lower_prime_ge_seven hp) (n-1) n⟩

theorem goldbach_lower_density_multiplicative (R z : ℝ) (n : ℤ) :
    GoldbachMultiplicativeDensityOn (goldbachLowerSievePrimes z)
      (goldbachPrimeDensityProduct (goldbachLowerDensity R n)) := by
  classical
  refine ⟨?_,?_,?_⟩
  · simp only [goldbachPrimeDensityProduct,Nat.primeFactors_one,prod_empty]
  · intro d e hd he hc _ _
    simp only [goldbachPrimeDensityProduct,Nat.primeFactors_mul hd.ne_zero he.ne_zero,
      prod_union hc.disjoint_primeFactors]
  · intro p hp
    have hs := ((mem_goldbach_lower_sieve_primes z p).mp hp).1
    simpa only [goldbachPrimeDensityProduct,hs.1.primeFactors,prod_singleton] using
      goldbach_lower_prime_density_range R n hs

theorem goldbach_lower_preliminary_dimension (K R z Z : ℝ)
    (hM : GoldbachClassicalIntervalMertens K) (n : ℤ) :
    GoldbachRefinedSieveDimension (goldbachLowerPreliminaryPrimes R z) Z 2 K
      (goldbachPrimeDensityProduct (goldbachLowerDensity R n)) := by
  classical
  intro w y hw hwy _
  let S := (goldbachLowerPreliminaryPrimes R z).filter
    (fun p : ℕ=>w≤(p:ℝ) ∧ (p:ℝ)<y)
  have hS : ∀ p∈S,p.Prime ∧ 7≤p ∧ w≤(p:ℝ) ∧ (p:ℝ)<y := by
    intro p hp
    obtain ⟨hp,hwin⟩ := mem_filter.mp hp
    have hs := ((mem_goldbach_lower_sieve_primes z p).mp (mem_filter.mp hp).1).1
    exact ⟨hs.1,goldbach_lower_prime_ge_seven hs,hwin⟩
  have hprod : (∏ p∈S,(1-goldbachPrimeDensityProduct (goldbachLowerDensity R n) p)⁻¹)≤
      ∏ p∈S,(1-2/((p:ℝ)-3))⁻¹ := by
    apply prod_le_prod₀
    · intro p hp
      have hs := ((mem_goldbach_lower_sieve_primes z p).mp (mem_filter.mp (mem_filter.mp hp).1).1).1
      rw [goldbachPrimeDensityProduct,hs.1.primeFactors,prod_singleton]
      exact inv_nonneg.mpr (sub_pos.mpr (goldbach_lower_prime_density_range R n hs).2).le
    · intro p hp
      have hs := hS p hp
      have : Fact p.Prime := ⟨hs.1⟩
      rw [goldbachPrimeDensityProduct,hs.1.primeFactors,prod_singleton]
      have hb := goldbach_local_density_le R p (by omega) (n-1) n
      have hpos : 0<1-2/((p:ℝ)-3) := sub_pos.mpr (goldbach_density_bound_lt_one p hs.2.1)
      simpa only [one_div,goldbachLowerDensity] using
        one_div_le_one_div_of_le hpos (sub_le_sub_left hb 1)
  exact hprod.trans (hM.preliminary w y S hw hwy hS)

theorem goldbach_lower_outer_dimension (K R z : ℝ)
    (hM : GoldbachClassicalIntervalMertens K) (n : ℤ) :
    GoldbachRefinedSieveDimension (goldbachLowerOuterPrimes R z) z ((1:ℝ)/2) K
      (goldbachPrimeDensityProduct (goldbachLowerDensity R n)) := by
  classical
  intro w y hw hwy _
  let S := (goldbachLowerOuterPrimes R z).filter
    (fun p : ℕ=>w≤(p:ℝ) ∧ (p:ℝ)<y)
  have hS : ∀ p∈S,GoldbachFixedLowerSievePrime p ∧ w≤(p:ℝ) ∧ (p:ℝ)<y := by
    intro p hp
    obtain ⟨hp,hwin⟩ := mem_filter.mp hp
    exact ⟨((mem_goldbach_lower_sieve_primes z p).mp (mem_filter.mp hp).1).1,hwin⟩
  have he : (∏ p∈S,(1-goldbachPrimeDensityProduct (goldbachLowerDensity R n) p)⁻¹)=
      ∏ p∈S,(1-1/((p:ℝ)-1))⁻¹ := by
    apply prod_congr rfl
    intro p hp
    have hs := (hS p hp).1
    have hR := (mem_filter.mp (mem_filter.mp hp).1).2
    simp only [goldbachPrimeDensityProduct,hs.1.primeFactors,prod_singleton,
      goldbachLowerDensity,goldbachLocalDensity,ite_eq_right (not_le.mpr hR)]
  exact he.trans_le (hM.half w y S hw hwy hS)

end PrimeSquares

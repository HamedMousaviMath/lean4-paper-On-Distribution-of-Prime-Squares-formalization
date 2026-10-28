import PrimeSquares.GeneralCoefficient

/-!
# Finite support and Euler product with an arbitrary integer multiplier

The support is proved from pointwise quadratic Cohen vanishing, independently
of ell. The sum is reduced to divisors of the same explicit factorial cube.
-/

open Finset

namespace PrimeSquares

noncomputable def smoothGeneralSeries (Q k : ℕ) (ell b n : ℤ) : ℂ :=
  ∑' q : ℕ, if ∀ p ∈ q.primeFactors, p < Q then generalCoefficient q k ell b n else 0

/-- Nonzero smooth coefficients divide one explicit positive integer. -/
theorem generalCoefficient_nonzero_dvd_bound (Q k : ℕ) [NeZero k] (ell b x : ℤ)
    (hQ : 3 ≤ Q) (q : ℕ) (hs : ∀ p ∈ q.primeFactors, p < Q)
    (hf : generalCoefficient q k ell b x ≠ 0) : q ∣ smoothEulerBound Q := by
  have hq : q ≠ 0 := by
    intro hz
    exact hf (by simp [hz, generalCoefficient])
  have : NeZero q := ⟨hq⟩
  have hN : smoothEulerBound Q ≠ 0 := pow_ne_zero _ (Nat.factorial_ne_zero _)
  apply (Nat.factorization_le_iff_dvd hq hN).mp
  intro p
  by_cases hz : q.factorization p = 0
  · rw [hz]
    exact Nat.zero_le _
  have hm : p ∈ q.primeFactors := by
    change p ∈ q.factorization.support
    exact Finsupp.mem_support_iff.mpr hz
  have hp : p.Prime := Nat.prime_of_mem_primeFactors hm
  have : Fact p.Prime := ⟨hp⟩
  have hν : q.factorization p ≤ 3 := by
    by_contra! hν
    by_cases hp2 : p = 2
    · subst p
      exact hf (generalCoefficient_sixteen_dvd q k
        ((Nat.prime_two.pow_dvd_iff_le_factorization (k := 4) hq).mpr (by omega)) ell b x)
    · exact hf (generalCoefficient_odd_prime_sq q k p hp2
        ((hp.pow_dvd_iff_le_factorization (k := 2) hq).mpr (by omega)) ell b x)
  have hd : p ∣ (Q - 1).factorial := hp.dvd_factorial.mpr (by have := hs p hm; omega)
  have hval : 1 ≤ ((Q - 1).factorial).factorization p :=
    (hp.pow_dvd_iff_le_factorization (Nat.factorial_ne_zero _)).mp (by simpa using hd)
  simp only [smoothEulerBound, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
  omega

/-- The series is literally a finite divisor sum, with vanishing proved outside it. -/
theorem smoothGeneralSeries_eq_divisor_sum (Q k : ℕ) [NeZero k] (ell b x : ℤ)
    (hQ : 3 ≤ Q) : smoothGeneralSeries Q k ell b x =
      ∑ q ∈ (smoothEulerBound Q).divisors, generalCoefficient q k ell b x := by
  classical
  have hN : smoothEulerBound Q ≠ 0 := pow_ne_zero _ (Nat.factorial_ne_zero _)
  unfold smoothGeneralSeries
  rw [tsum_eq_sum (s := (smoothEulerBound Q).divisors)]
  · apply sum_congr rfl
    intro q hq
    exact ite_eq_left (smoothEulerBound_divisor_smooth Q hQ q (Nat.mem_divisors.mp hq).1)
  · intro q hq
    by_cases hs : ∀ p ∈ q.primeFactors, p < Q
    · rw [ite_eq_left hs]
      by_contra hf
      exact hq (Nat.mem_divisors.mpr
        ⟨generalCoefficient_nonzero_dvd_bound Q k ell b x hQ q hs hf, hN⟩)
    · exact ite_eq_right hs

/-- Finite divisor factorization for the genuine coefficients. -/
theorem generalCoefficient_divisor_product (N k : ℕ) [NeZero k] (ell b x : ℤ)
    (hN : N ≠ 0) : (∑ q ∈ N.divisors, generalCoefficient q k ell b x) =
      ∏ p ∈ N.primeFactors, ∑ j ∈ range (N.factorization p + 1),
        generalCoefficient (p ^ j) k ell b x := by
  exact sum_divisors_multiplicative (fun q => generalCoefficient q k ell b x)
    (by simp [generalCoefficient]) (generalCoefficient_one k ell b x)
    (fun m n h => generalCoefficient_mul m n k h ell b x) N hN

/-- The local exponent sum at an odd prime has just two terms. -/
theorem general_odd_exponent_sum (p k a : ℕ) [Fact p.Prime] [NeZero k]
    (hp2 : p ≠ 2) (ha : 1 ≤ a) (ell b x : ℤ) :
    (∑ j ∈ range (a + 1), generalCoefficient (p ^ j) k ell b x) =
      1 + generalCoefficient p k ell b x := by
  classical
  have hp : p.Prime := Fact.out
  have he : (∑ j ∈ range (a + 1), generalCoefficient (p ^ j) k ell b x) =
      ∑ j ∈ range 2, generalCoefficient (p ^ j) k ell b x := by
    symm
    apply sum_subset (range_mono (by omega))
    intro j _ hj
    have hj2 : 2 ≤ j := by simpa only [mem_range, not_lt] using hj
    exact generalCoefficient_odd_prime_sq (p ^ j) k p hp2 (Nat.pow_dvd_pow p hj2) ell b x
  rw [he]
  simp [sum_range_succ, generalCoefficient_one]

/-- The local exponent sum at two has just the exponents zero through three. -/
theorem general_two_exponent_sum (k a : ℕ) [NeZero k] (ha : 3 ≤ a) (ell b x : ℤ) :
    (∑ j ∈ range (a + 1), generalCoefficient (2 ^ j) k ell b x) =
      1 + generalCoefficient 2 k ell b x + generalCoefficient 4 k ell b x +
        generalCoefficient 8 k ell b x := by
  classical
  have he : (∑ j ∈ range (a + 1), generalCoefficient (2 ^ j) k ell b x) =
      ∑ j ∈ range 4, generalCoefficient (2 ^ j) k ell b x := by
    symm
    apply sum_subset (range_mono (by omega))
    intro j _ hj
    have hj4 : 4 ≤ j := by simpa only [mem_range, not_lt] using hj
    exact generalCoefficient_sixteen_dvd (2 ^ j) k (Nat.pow_dvd_pow 2 hj4) ell b x
  rw [he]
  norm_num [sum_range_succ, generalCoefficient_one]

/-- The series equals a finite Euler product of its actual local coefficients. -/
theorem smoothGeneralSeries_euler_product (Q k : ℕ) [NeZero k] (ell b x : ℤ)
    (hQ : 3 ≤ Q) : smoothGeneralSeries Q k ell b x =
      (1 + generalCoefficient 2 k ell b x + generalCoefficient 4 k ell b x +
        generalCoefficient 8 k ell b x) *
      ∏ p ∈ oddPrimesBelow Q, (1 + generalCoefficient p k ell b x) := by
  classical
  have hN : smoothEulerBound Q ≠ 0 := pow_ne_zero _ (Nat.factorial_ne_zero _)
  rw [smoothGeneralSeries_eq_divisor_sum Q k ell b x hQ,
    generalCoefficient_divisor_product _ k ell b x hN]
  have hset : (smoothEulerBound Q).primeFactors = insert 2 (oddPrimesBelow Q) := by
    ext p
    rw [smoothEulerBound_primeFactors Q hQ]
    simp only [mem_insert, oddPrimesBelow, mem_filter, mem_range]
    constructor
    · rintro ⟨hp, hpQ⟩
      by_cases he : p = 2
      · exact Or.inl he
      · exact Or.inr ⟨hpQ, hp, by have := hp.two_le; omega⟩
    · rintro (rfl | hp)
      · exact ⟨Nat.prime_two, by omega⟩
      · exact ⟨hp.2.1, hp.1⟩
  have h2 : 3 ≤ (smoothEulerBound Q).factorization 2 :=
    smoothEulerBound_factorization_ge_three Q hQ 2
      ((smoothEulerBound_primeFactors Q hQ 2).mpr ⟨Nat.prime_two, by omega⟩)
  rw [hset, prod_insert (by simp [oddPrimesBelow])]
  rw [general_two_exponent_sum k _ h2 ell b x]
  congr 1
  apply prod_congr rfl
  intro p hp
  obtain ⟨_, hp', hp2⟩ := mem_filter.mp hp
  have : Fact p.Prime := ⟨hp'⟩
  have hmem : p ∈ (smoothEulerBound Q).primeFactors := by
    rw [hset]
    exact mem_insert_of_mem (by exact (mem_filter.mpr ⟨‹p ∈ range Q›, hp', hp2⟩))
  exact general_odd_exponent_sum p k _ (ne_of_gt hp2)
    (by have := smoothEulerBound_factorization_ge_three Q hQ p hmem; omega) ell b x

end PrimeSquares

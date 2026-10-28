import PrimeSquares.SmoothEuler

/-!
# The smooth absolute Cohen series

Source: Lemma 3.20, `l:lowramanujan`. This module proves its actual finite
Euler product and a uniform local majorant. The logarithmic estimate is
assembled separately after proving the elementary prime-product bound.
-/

open Finset

namespace PrimeSquares

noncomputable def cohenWeight (q : ℕ) (n : ℤ) : ℝ :=
  ‖cohenCorrelation q n‖ / ((q : ℝ) * (q.totient : ℝ))

noncomputable def smoothCohenSeries (Q : ℕ) (n : ℤ) : ℝ :=
  ∑' q : ℕ, if ∀ p ∈ q.primeFactors, p < Q then cohenWeight q n else 0

/-- At a positive modulus this is exactly the absolute sum in the source lemma. -/
theorem cohenWeight_eq (q : ℕ) [NeZero q] (n : ℤ) :
    cohenWeight q n = (1 / ((q : ℝ) * (q.totient : ℝ))) *
      ‖∑ u : (ZMod q)ˣ, ramanujanSum q ((n : ZMod q) - (u : ZMod q) ^ 2)‖ := by
  rw [cohenWeight, cohenCorrelation_eq, quadraticRamanujanSum,
    sum_unit_filter_eq_sum_units]
  ring

theorem cohenWeight_nonneg (q : ℕ) (n : ℤ) : 0 ≤ cohenWeight q n := by
  exact div_nonneg (norm_nonneg _) (by positivity)

theorem cohenWeight_zero (n : ℤ) : cohenWeight 0 n = 0 := by
  simp [cohenWeight]

theorem cohenWeight_one (n : ℤ) : cohenWeight 1 n = 1 := by
  simp [cohenWeight, cohenCorrelation_eq, quadraticRamanujanSum_one]

theorem cohenWeight_mul (m r : ℕ) (hc : m.Coprime r) (n : ℤ) :
    cohenWeight (m * r) n = cohenWeight m n * cohenWeight r n := by
  simp only [cohenWeight, cohenCorrelation_mul m r hc, norm_mul,
    Nat.cast_mul, Nat.totient_mul hc, div_mul_div_comm]
  ring

theorem cohenWeight_odd_prime_sq (q p : ℕ) [NeZero q] [Fact p.Prime]
    (hp2 : p ≠ 2) (hd : p ^ 2 ∣ q) (n : ℤ) : cohenWeight q n = 0 := by
  simp [cohenWeight, cohenCorrelation_eq_zero_of_odd_prime_sq q p (NeZero.ne q) hp2 hd]

theorem cohenWeight_sixteen_dvd (q : ℕ) [NeZero q] (hd : 16 ∣ q) (n : ℤ) :
    cohenWeight q n = 0 := by
  simp [cohenWeight, cohenCorrelation_eq_zero_of_sixteen_dvd q (NeZero.ne q) hd]

/-- Nonzero smooth coefficients divide one explicit positive integer. -/
theorem cohenWeight_nonzero_dvd_bound (Q : ℕ) (x : ℤ)
    (hQ : 3 ≤ Q) (q : ℕ) (hs : ∀ p ∈ q.primeFactors, p < Q)
    (hf : cohenWeight q x ≠ 0) : q ∣ smoothEulerBound Q := by
  have hq : q ≠ 0 := by
    intro hz
    exact hf (by simp [hz, cohenWeight])
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
      exact hf (cohenWeight_sixteen_dvd q
        ((Nat.prime_two.pow_dvd_iff_le_factorization (k := 4) hq).mpr (by omega)) x)
    · exact hf (cohenWeight_odd_prime_sq q p hp2
        ((hp.pow_dvd_iff_le_factorization (k := 2) hq).mpr (by omega)) x)
  have hd : p ∣ (Q - 1).factorial := hp.dvd_factorial.mpr (by have := hs p hm; omega)
  have hval : 1 ≤ ((Q - 1).factorial).factorization p :=
    (hp.pow_dvd_iff_le_factorization (Nat.factorial_ne_zero _)).mp (by simpa using hd)
  simp only [smoothEulerBound, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
  omega

/-- The series is literally a finite divisor sum, with vanishing proved outside it. -/
theorem smoothCohenSeries_eq_divisor_sum (Q : ℕ) (x : ℤ)
    (hQ : 3 ≤ Q) : smoothCohenSeries Q x =
      ∑ q ∈ (smoothEulerBound Q).divisors, cohenWeight q x := by
  classical
  have hN : smoothEulerBound Q ≠ 0 := pow_ne_zero _ (Nat.factorial_ne_zero _)
  unfold smoothCohenSeries
  rw [tsum_eq_sum (s := (smoothEulerBound Q).divisors)]
  · apply sum_congr rfl
    intro q hq
    exact ite_eq_left (smoothEulerBound_divisor_smooth Q hQ q (Nat.mem_divisors.mp hq).1)
  · intro q hq
    by_cases hs : ∀ p ∈ q.primeFactors, p < Q
    · rw [ite_eq_left hs]
      by_contra hf
      exact hq (Nat.mem_divisors.mpr
        ⟨cohenWeight_nonzero_dvd_bound Q x hQ q hs hf, hN⟩)
    · exact ite_eq_right hs

/-- Finite divisor factorization for the genuine coefficients. -/
theorem cohenWeight_divisor_product (N : ℕ) (x : ℤ)
    (hN : N ≠ 0) : (∑ q ∈ N.divisors, cohenWeight q x) =
      ∏ p ∈ N.primeFactors, ∑ j ∈ range (N.factorization p + 1),
        cohenWeight (p ^ j) x := by
  exact sum_divisors_multiplicative (fun q => cohenWeight q x)
    (by simp [cohenWeight]) (cohenWeight_one x)
    (fun m n h => cohenWeight_mul m n h x) N hN

/-- The local exponent sum at an odd prime has just two terms. -/
theorem cohenWeight_odd_exponent_sum (p a : ℕ) [Fact p.Prime]
    (hp2 : p ≠ 2) (ha : 1 ≤ a) (x : ℤ) :
    (∑ j ∈ range (a + 1), cohenWeight (p ^ j) x) =
      1 + cohenWeight p x := by
  classical
  have hp : p.Prime := Fact.out
  have he : (∑ j ∈ range (a + 1), cohenWeight (p ^ j) x) =
      ∑ j ∈ range 2, cohenWeight (p ^ j) x := by
    symm
    apply sum_subset (range_mono (by omega))
    intro j _ hj
    have hj2 : 2 ≤ j := by simpa only [mem_range, not_lt] using hj
    exact cohenWeight_odd_prime_sq (p ^ j) p hp2 (Nat.pow_dvd_pow p hj2) x
  rw [he]
  simp [sum_range_succ, cohenWeight_one]

/-- The local exponent sum at two has just the exponents zero through three. -/
theorem cohenWeight_two_exponent_sum (a : ℕ) (ha : 3 ≤ a) (x : ℤ) :
    (∑ j ∈ range (a + 1), cohenWeight (2 ^ j) x) =
      1 + cohenWeight 2 x + cohenWeight 4 x +
        cohenWeight 8 x := by
  classical
  have he : (∑ j ∈ range (a + 1), cohenWeight (2 ^ j) x) =
      ∑ j ∈ range 4, cohenWeight (2 ^ j) x := by
    symm
    apply sum_subset (range_mono (by omega))
    intro j _ hj
    have hj4 : 4 ≤ j := by simpa only [mem_range, not_lt] using hj
    exact cohenWeight_sixteen_dvd (2 ^ j) (Nat.pow_dvd_pow 2 hj4) x
  rw [he]
  norm_num [sum_range_succ, cohenWeight_one]

/-- The series equals a finite Euler product of its actual local coefficients. -/
theorem smoothCohenSeries_euler_product (Q : ℕ) (x : ℤ)
    (hQ : 3 ≤ Q) : smoothCohenSeries Q x =
      (1 + cohenWeight 2 x + cohenWeight 4 x +
        cohenWeight 8 x) *
      ∏ p ∈ oddPrimesBelow Q, (1 + cohenWeight p x) := by
  classical
  have hN : smoothEulerBound Q ≠ 0 := pow_ne_zero _ (Nat.factorial_ne_zero _)
  rw [smoothCohenSeries_eq_divisor_sum Q x hQ,
    cohenWeight_divisor_product _ x hN]
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
  rw [cohenWeight_two_exponent_sum _ h2 x]
  congr 1
  apply prod_congr rfl
  intro p hp
  obtain ⟨_, hp', hp2⟩ := mem_filter.mp hp
  have : Fact p.Prime := ⟨hp'⟩
  have hmem : p ∈ (smoothEulerBound Q).primeFactors := by
    rw [hset]
    exact mem_insert_of_mem (by exact (mem_filter.mpr ⟨‹p ∈ range Q›, hp', hp2⟩))
  exact cohenWeight_odd_exponent_sum p _ (ne_of_gt hp2)
    (by have := smoothEulerBound_factorization_ge_three Q hQ p hmem; omega) x

/-- Exact small-prime estimates give a uniform factor at two. -/
theorem cohenWeight_two_factor_le (x : ℤ) :
    1 + cohenWeight 2 x + cohenWeight 4 x + cohenWeight 8 x ≤ (5 / 2 : ℝ) := by
  have h2 : cohenWeight 2 x ≤ (1 / 2 : ℝ) := by
    have he := cohenCorrelation_two_pow 1 x
    change cohenCorrelation 2 x = _ at he
    rw [cohenWeight, he]
    norm_num only [twoAdicCohenFactor, show Nat.totient 2 = 1 by decide]
    split_ifs <;> norm_num
  have h4 : cohenWeight 4 x ≤ (1 / 2 : ℝ) := by
    have he := cohenCorrelation_two_pow 2 x
    change cohenCorrelation 4 x = _ at he
    rw [cohenWeight, he]
    norm_num only [twoAdicCohenFactor, show Nat.totient 4 = 2 by decide]
    split_ifs <;> norm_num
  have h8 : cohenWeight 8 x ≤ (1 / 2 : ℝ) := by
    have he := cohenCorrelation_two_pow 3 x
    change cohenCorrelation 8 x = _ at he
    rw [cohenWeight, he]
    norm_num only [twoAdicCohenFactor, show Nat.totient 8 = 4 by decide]
    split_ifs <;> norm_num
  linarith

/-- Every odd-prime weight has the same uniform majorant. -/
theorem cohenWeight_odd_prime_le (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (x : ℤ) :
    cohenWeight p x ≤ ((p : ℝ) + 1) / ((p : ℝ) * ((p : ℝ) - 1)) := by
  have hp : p.Prime := Fact.out
  have he : cohenCorrelation p x = oddCohenFactor p x := by
    simpa using cohenCorrelation_odd_prime_pow p hp2 1 (by decide) x
  rw [cohenWeight, he, Nat.totient_prime hp, Nat.cast_sub hp.one_le, Nat.cast_one]
  exact div_le_div_of_nonneg_right (norm_oddCohenFactor_le p x)
    (mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr (by exact_mod_cast hp.one_le)))

/-- The entire actual series is bounded by one explicit finite prime product. -/
theorem smoothCohenSeries_le_prime_product (Q : ℕ) (x : ℤ) (hQ : 3 ≤ Q) :
    smoothCohenSeries Q x ≤ (5 / 2 : ℝ) *
      ∏ p ∈ oddPrimesBelow Q, (1 + ((p : ℝ) + 1) / ((p : ℝ) * ((p : ℝ) - 1))) := by
  rw [smoothCohenSeries_euler_product Q x hQ]
  apply mul_le_mul (cohenWeight_two_factor_le x)
  · apply prod_le_prod₀
    · intro p _
      exact add_nonneg zero_le_one (cohenWeight_nonneg p x)
    · intro p hp
      have : Fact p.Prime := ⟨(mem_filter.mp hp).2.1⟩
      simpa only [add_comm] using add_le_add_left (cohenWeight_odd_prime_le p
        (ne_of_gt (mem_filter.mp hp).2.2) x) 1
  · exact prod_nonneg (fun p _ => add_nonneg zero_le_one (cohenWeight_nonneg p x))
  · norm_num

end PrimeSquares

import PrimeSquares.EulerCoefficient
import Mathlib.Data.Nat.Prime.Factorial

/-!
# A finite-support Euler product for the actual smooth-modulus series

Source: Draft5, Lemma 3.14. The cutoff is an integer Q>=3. Smoothness means
that every prime divisor is below Q; at q=1 this agrees with P^+(1)=1 in
this range. The coefficient at q=0 is zero. A factorial cube gives a finite
divisor set containing every possible nonzero term, so no convergence or
rearrangement assumption is needed.
-/

open Finset
open scoped ArithmeticFunction.zeta

namespace PrimeSquares

def oddPrimesBelow (Q : ℕ) : Finset ℕ := (range Q).filter fun p => p.Prime ∧ 2 < p

def smoothEulerBound (Q : ℕ) : ℕ := ((Q - 1).factorial) ^ 3

noncomputable def smoothProgressionSeries (Q k : ℕ) (b x : ℤ) : ℂ :=
  ∑' q : ℕ, if ∀ p ∈ q.primeFactors, p < Q then progressionCoefficient q k b x else 0

/-- The classical divisor Euler product, applied only to finite divisor sums. -/
theorem sum_divisors_multiplicative {R : Type*} [CommSemiring R] (f : ℕ → R) (hf0 : f 0 = 0) (hf1 : f 1 = 1)
    (hfm : ∀ m n, m.Coprime n → f (m * n) = f m * f n) (N : ℕ) (hN : N ≠ 0) :
    (∑ d ∈ N.divisors, f d) =
      ∏ p ∈ N.primeFactors, ∑ j ∈ range (N.factorization p + 1), f (p ^ j) := by
  let F : ArithmeticFunction R := ⟨f, hf0⟩
  have hF : F.IsMultiplicative := ⟨hf1, fun h => hfm _ _ h⟩
  have hG : (F * (ζ : ArithmeticFunction R)).IsMultiplicative :=
    hF.mul ArithmeticFunction.isMultiplicative_zeta.natCast
  have he := Nat.multiplicative_factorization (fun n => (F * (ζ : ArithmeticFunction R)) n)
    (fun m n h => hG.map_mul_of_coprime h) hG.map_one hN
  simp only [ArithmeticFunction.coe_mul_zeta_apply] at he
  change (∑ d ∈ N.divisors, f d) =
    ∏ p ∈ N.primeFactors, ∑ d ∈ (p ^ N.factorization p).divisors, f d at he
  rw [he]
  apply prod_congr rfl
  intro p hp
  exact Nat.sum_divisors_prime_pow (Nat.prime_of_mem_primeFactors hp)

/-- Nonzero smooth coefficients divide one explicit positive integer. -/
theorem progressionCoefficient_nonzero_dvd_bound (Q k : ℕ) [NeZero k] (b x : ℤ)
    (hQ : 3 ≤ Q) (q : ℕ) (hs : ∀ p ∈ q.primeFactors, p < Q)
    (hf : progressionCoefficient q k b x ≠ 0) : q ∣ smoothEulerBound Q := by
  have hq : q ≠ 0 := by
    intro hz
    exact hf (by simp [hz, progressionCoefficient])
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
      exact hf (progressionCoefficient_sixteen_dvd q k
        ((Nat.prime_two.pow_dvd_iff_le_factorization (k := 4) hq).mpr (by omega)) b x)
    · exact hf (progressionCoefficient_odd_prime_sq q k p hp2
        ((hp.pow_dvd_iff_le_factorization (k := 2) hq).mpr (by omega)) b x)
  have hd : p ∣ (Q - 1).factorial := hp.dvd_factorial.mpr (by have := hs p hm; omega)
  have hval : 1 ≤ ((Q - 1).factorial).factorization p :=
    (hp.pow_dvd_iff_le_factorization (Nat.factorial_ne_zero _)).mp (by simpa using hd)
  simp only [smoothEulerBound, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
  omega

/-- Every divisor of the bound has only primes below Q. -/
theorem smoothEulerBound_divisor_smooth (Q : ℕ) (hQ : 3 ≤ Q) (q : ℕ)
    (hd : q ∣ smoothEulerBound Q) : ∀ p ∈ q.primeFactors, p < Q := by
  intro p hpq
  have hp := Nat.prime_of_mem_primeFactors hpq
  have hdN := (Nat.dvd_of_mem_primeFactors hpq).trans hd
  have hdf : p ∣ (Q - 1).factorial := hp.dvd_of_dvd_pow hdN
  have := hp.dvd_factorial.mp hdf
  omega

/-- The series is literally a finite divisor sum, with vanishing proved outside it. -/
theorem smoothProgressionSeries_eq_divisor_sum (Q k : ℕ) [NeZero k] (b x : ℤ)
    (hQ : 3 ≤ Q) : smoothProgressionSeries Q k b x =
      ∑ q ∈ (smoothEulerBound Q).divisors, progressionCoefficient q k b x := by
  classical
  have hN : smoothEulerBound Q ≠ 0 := pow_ne_zero _ (Nat.factorial_ne_zero _)
  unfold smoothProgressionSeries
  rw [tsum_eq_sum (s := (smoothEulerBound Q).divisors)]
  · apply sum_congr rfl
    intro q hq
    exact ite_eq_left (smoothEulerBound_divisor_smooth Q hQ q (Nat.mem_divisors.mp hq).1)
  · intro q hq
    by_cases hs : ∀ p ∈ q.primeFactors, p < Q
    · rw [ite_eq_left hs]
      by_contra hf
      exact hq (Nat.mem_divisors.mpr
        ⟨progressionCoefficient_nonzero_dvd_bound Q k b x hQ q hs hf, hN⟩)
    · exact ite_eq_right hs

/-- Finite divisor factorization for the genuine coefficients. -/
theorem progressionCoefficient_divisor_product (N k : ℕ) [NeZero k] (b x : ℤ)
    (hN : N ≠ 0) : (∑ q ∈ N.divisors, progressionCoefficient q k b x) =
      ∏ p ∈ N.primeFactors, ∑ j ∈ range (N.factorization p + 1),
        progressionCoefficient (p ^ j) k b x := by
  exact sum_divisors_multiplicative (fun q => progressionCoefficient q k b x)
    (by simp [progressionCoefficient]) (progressionCoefficient_one k b x)
    (fun m n h => progressionCoefficient_mul m n k h b x) N hN

/-- The local exponent sum at an odd prime has just two terms. -/
theorem coefficient_odd_exponent_sum (p k a : ℕ) [Fact p.Prime] [NeZero k]
    (hp2 : p ≠ 2) (ha : 1 ≤ a) (b x : ℤ) :
    (∑ j ∈ range (a + 1), progressionCoefficient (p ^ j) k b x) =
      1 + progressionCoefficient p k b x := by
  classical
  have hp : p.Prime := Fact.out
  have he : (∑ j ∈ range (a + 1), progressionCoefficient (p ^ j) k b x) =
      ∑ j ∈ range 2, progressionCoefficient (p ^ j) k b x := by
    symm
    apply sum_subset (range_mono (by omega))
    intro j _ hj
    have hj2 : 2 ≤ j := by simpa only [mem_range, not_lt] using hj
    exact progressionCoefficient_odd_prime_sq (p ^ j) k p hp2 (Nat.pow_dvd_pow p hj2) b x
  rw [he]
  simp [sum_range_succ, progressionCoefficient_one]

/-- The local exponent sum at two has just the exponents zero through three. -/
theorem coefficient_two_exponent_sum (k a : ℕ) [NeZero k] (ha : 3 ≤ a) (b x : ℤ) :
    (∑ j ∈ range (a + 1), progressionCoefficient (2 ^ j) k b x) =
      1 + progressionCoefficient 2 k b x + progressionCoefficient 4 k b x +
        progressionCoefficient 8 k b x := by
  classical
  have he : (∑ j ∈ range (a + 1), progressionCoefficient (2 ^ j) k b x) =
      ∑ j ∈ range 4, progressionCoefficient (2 ^ j) k b x := by
    symm
    apply sum_subset (range_mono (by omega))
    intro j _ hj
    have hj4 : 4 ≤ j := by simpa only [mem_range, not_lt] using hj
    exact progressionCoefficient_sixteen_dvd (2 ^ j) k (Nat.pow_dvd_pow 2 hj4) b x
  rw [he]
  norm_num [sum_range_succ, progressionCoefficient_one]

/-- The divisor bound has exactly the primes below Q. -/
theorem smoothEulerBound_primeFactors (Q : ℕ) (hQ : 3 ≤ Q) (p : ℕ) :
    p ∈ (smoothEulerBound Q).primeFactors ↔ p.Prime ∧ p < Q := by
  constructor
  · intro hp
    exact ⟨Nat.prime_of_mem_primeFactors hp,
      smoothEulerBound_divisor_smooth Q hQ _ (dvd_refl _) p hp⟩
  · rintro ⟨hp, hpQ⟩
    have hd : p ∣ (Q - 1).factorial := hp.dvd_factorial.mpr (by omega)
    exact Nat.mem_primeFactors.mpr ⟨hp, dvd_pow hd (by decide : 3 ≠ 0),
      pow_ne_zero _ (Nat.factorial_ne_zero _)⟩

/-- Every prime exponent in the bound is at least three. -/
theorem smoothEulerBound_factorization_ge_three (Q : ℕ) (hQ : 3 ≤ Q) (p : ℕ)
    (hp : p ∈ (smoothEulerBound Q).primeFactors) : 3 ≤ (smoothEulerBound Q).factorization p := by
  obtain ⟨hp', hpQ⟩ := (smoothEulerBound_primeFactors Q hQ p).mp hp
  have hd : p ∣ (Q - 1).factorial := hp'.dvd_factorial.mpr (by omega)
  have he : 1 ≤ ((Q - 1).factorial).factorization p :=
    (hp'.pow_dvd_iff_le_factorization (Nat.factorial_ne_zero _)).mp (by simpa using hd)
  simp only [smoothEulerBound, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
  omega

/-- The series equals a finite Euler product of its actual local coefficients. -/
theorem smoothProgressionSeries_euler_product (Q k : ℕ) [NeZero k] (b x : ℤ)
    (hQ : 3 ≤ Q) : smoothProgressionSeries Q k b x =
      (1 + progressionCoefficient 2 k b x + progressionCoefficient 4 k b x +
        progressionCoefficient 8 k b x) *
      ∏ p ∈ oddPrimesBelow Q, (1 + progressionCoefficient p k b x) := by
  classical
  have hN : smoothEulerBound Q ≠ 0 := pow_ne_zero _ (Nat.factorial_ne_zero _)
  rw [smoothProgressionSeries_eq_divisor_sum Q k b x hQ,
    progressionCoefficient_divisor_product _ k b x hN]
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
  rw [coefficient_two_exponent_sum k _ h2 b x]
  congr 1
  apply prod_congr rfl
  intro p hp
  obtain ⟨_, hp', hp2⟩ := mem_filter.mp hp
  have : Fact p.Prime := ⟨hp'⟩
  have hmem : p ∈ (smoothEulerBound Q).primeFactors := by
    rw [hset]
    exact mem_insert_of_mem (by exact (mem_filter.mpr ⟨‹p ∈ range Q›, hp', hp2⟩))
  exact coefficient_odd_exponent_sum p k _ (ne_of_gt hp2)
    (by have := smoothEulerBound_factorization_ge_three Q hQ p hmem; omega) b x

end PrimeSquares

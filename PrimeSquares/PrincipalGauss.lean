import PrimeSquares.ProgressionCorrelation
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Actual principal quadratic Gauss sums

Source: the finite arithmetic part of Lemma 3.21. The complete prime sum is
evaluated in norm by a finite change of variables and character orthogonality.
The existing square-zero shift proves all prime-power vanishings.
-/

open Finset

namespace PrimeSquares

theorem norm_stdAddChar (q : ℕ) [NeZero q] (x : ZMod q) :
    ‖ZMod.stdAddChar x‖ = 1 := by
  simp only [ZMod.stdAddChar_apply, Circle.norm_coe]

theorem conj_stdAddChar (q : ℕ) [NeZero q] (x : ZMod q) :
    (starRingEnd ℂ) (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) := by
  rw [ZMod.stdAddChar_apply, ZMod.stdAddChar_apply,
    AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj]

noncomputable def completeQuadraticGaussSum (q : ℕ) [NeZero q] (a : ZMod q) : ℂ :=
  ∑ r : ZMod q, ZMod.stdAddChar (a * r ^ 2)

/-- Difference and sum coordinates are a bijection when two is invertible. -/
def sumDiffEquiv (p : ℕ) [Fact p.Prime] (h2 : (2 : ZMod p) ≠ 0) :
    (ZMod p × ZMod p) ≃ (ZMod p × ZMod p) where
  toFun uv := (uv.1 - uv.2, uv.1 + uv.2)
  invFun st := ((st.1 + st.2) / 2, (st.2 - st.1) / 2)
  left_inv uv := by
    apply Prod.ext <;> dsimp <;> field_simp <;> ring
  right_inv st := by
    apply Prod.ext <;> dsimp <;> field_simp <;> ring

theorem two_ne_zero_zmod_odd_prime (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    (2 : ZMod p) ≠ 0 := by
  have hp : p.Prime := Fact.out
  intro he
  have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp he
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2
  · exact hp.ne_one h1
  · exact hp2 h2

/-- The complete sum times its complex conjugate is exactly p. -/
theorem completeQuadraticGaussSum_mul_conj (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (a : ZMod p) (ha : a ≠ 0) :
    completeQuadraticGaussSum p a * (starRingEnd ℂ) (completeQuadraticGaussSum p a) =
      (p : ℂ) := by
  classical
  have h2 := two_ne_zero_zmod_odd_prime p hp2
  unfold completeQuadraticGaussSum
  rw [map_sum, sum_mul_sum]
  simp_rw [conj_stdAddChar, ← AddChar.map_add_eq_mul]
  calc
    _ = ∑ st : ZMod p × ZMod p, ZMod.stdAddChar (a * st.1 * st.2) := by
      rw [← Fintype.sum_prod_type (fun uv : ZMod p × ZMod p =>
        ZMod.stdAddChar (a * uv.1 ^ 2 + -(a * uv.2 ^ 2)))]
      apply Fintype.sum_equiv (sumDiffEquiv p h2)
      intro uv
      congr 1
      dsimp [sumDiffEquiv]
      ring
    _ = ∑ s : ZMod p, if s = 0 then (p : ℂ) else 0 := by
      rw [Fintype.sum_prod_type]
      apply sum_congr rfl
      intro s _
      change (∑ y : ZMod p, ZMod.stdAddChar ((a * s) * y)) = _
      rw [sum_stdAddChar_mul]
      simp only [mul_eq_zero, ha, false_or]
    _ = _ := by simp

theorem norm_completeQuadraticGaussSum_prime (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (a : ZMod p) (ha : a ≠ 0) : ‖completeQuadraticGaussSum p a‖ = Real.sqrt p := by
  have he := completeQuadraticGaussSum_mul_conj p hp2 a ha
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq] at he
  have hsq : ‖completeQuadraticGaussSum p a‖ ^ 2 = (p : ℝ) := by
    exact_mod_cast he
  have hroot := Real.sqrt_sq (norm_nonneg (completeQuadraticGaussSum p a))
  rw [hsq] at hroot
  exact hroot.symm

/-- The unit prime sum is the complete prime sum with its zero term removed. -/
theorem unitQuadraticGaussSum_prime (p : ℕ) [Fact p.Prime] (a : ZMod p) :
    unitQuadraticGaussSum p a = completeQuadraticGaussSum p a - 1 := by
  classical
  rw [unitQuadraticGaussSum, ← sum_unit_filter_eq_sum_units p
    (fun r : ZMod p => ZMod.stdAddChar (a * r ^ 2))]
  have term (r : ZMod p) :
      (if IsUnit r then ZMod.stdAddChar (a * r ^ 2) else 0) =
        ZMod.stdAddChar (a * r ^ 2) - if r = 0 then 1 else 0 := by
    by_cases hr : r = 0
    · simp [hr, AddChar.map_zero_eq_one]
    · simp [isUnit_iff_ne_zero, hr]
  simp_rw [term]
  rw [sum_sub_distrib]
  simp only [sum_ite_eq', mem_univ, ite_true]
  rfl

theorem norm_unitQuadraticGaussSum_prime_le (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (a : ZMod p) (ha : IsUnit a) : ‖unitQuadraticGaussSum p a‖ ≤ Real.sqrt p + 1 := by
  rw [unitQuadraticGaussSum_prime]
  calc
    _ ≤ ‖completeQuadraticGaussSum p a‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = _ := by rw [norm_completeQuadraticGaussSum_prime p hp2 a ha.ne_zero, norm_one]

theorem principalSquareSum_as_unitGauss (q : ℕ) [NeZero q] (a : ZMod q) :
    principalSquareSum q a = (q.totient : ℂ)⁻¹ * unitQuadraticGaussSum q (-a) := by
  simp only [principalSquareSum, unitQuadraticGaussSum, neg_mul]

theorem norm_principalSquareSum (q : ℕ) [NeZero q] (a : ZMod q) :
    ‖principalSquareSum q a‖ = ‖unitQuadraticGaussSum q (-a)‖ / (q.totient : ℝ) := by
  rw [principalSquareSum_as_unitGauss, norm_mul, norm_inv, norm_natCast]
  ring

/-- The normalized sum is always bounded by one, including modulus one. -/
theorem norm_principalSquareSum_le_one (q : ℕ) [NeZero q] (a : ZMod q) :
    ‖principalSquareSum q a‖ ≤ 1 := by
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q))
  rw [norm_principalSquareSum]
  apply (div_le_iff₀ hφ).mpr
  calc
    _ ≤ ∑ u : (ZMod q)ˣ, ‖ZMod.stdAddChar (-(a * (u : ZMod q) ^ 2))‖ := by
      simpa only [unitQuadraticGaussSum, neg_mul] using
        norm_sum_le univ (fun u : (ZMod q)ˣ => ZMod.stdAddChar (-(a * (u : ZMod q) ^ 2)))
    _ = _ := by simp [ZMod.card_units_eq_totient]

/-- The actual unit sum vanishes at every odd prime power of exponent at least two. -/
theorem unitQuadraticGaussSum_odd_prime_pow (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (k : ℕ) (a : ZMod (p ^ (k + 2))) (ha : IsUnit a) :
    unitQuadraticGaussSum (p ^ (k + 2)) a = 0 := by
  have hp : p.Prime := Fact.out
  let t : ZMod (p ^ (k + 2)) := (p ^ (k + 1) : ℕ)
  have ht : t ^ 2 = 0 := by
    dsimp [t]
    rw [← Nat.cast_pow, ← pow_mul, ZMod.natCast_eq_zero_iff]
    exact Nat.pow_dvd_pow p (by omega)
  have h2t : 2 * t ≠ 0 := by
    intro h
    have hcast : ((2 * p ^ (k + 1) : ℕ) : ZMod (p ^ (k + 2))) = 0 := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using h
    have hd := (ZMod.natCast_eq_zero_iff _ _).mp hcast
    have hq : p ^ (k + 2) = p ^ (k + 1) * p := by
      rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]
    rw [hq, mul_comm 2 (p ^ (k + 1))] at hd
    have hd2 : p ∣ 2 := Nat.dvd_of_mul_dvd_mul_left (Nat.pow_pos hp.pos) hd
    rcases (Nat.dvd_prime Nat.prime_two).mp hd2 with h1 | h2
    · exact hp.ne_one h1
    · exact hp2 h2
  exact unitQuadraticGaussSum_eq_zero_of_square_zero _ t ht h2t a ha

/-- The actual unit sum vanishes at every power of two with exponent at least four. -/
theorem unitQuadraticGaussSum_two_pow_ge_four (k : ℕ) (a : ZMod (2 ^ (k + 4))) (ha : IsUnit a) :
    unitQuadraticGaussSum (2 ^ (k + 4)) a = 0 := by
  let t : ZMod (2 ^ (k + 4)) := (2 ^ (k + 2) : ℕ)
  have ht : t ^ 2 = 0 := by
    dsimp [t]
    rw [← Nat.cast_pow, ← pow_mul, ZMod.natCast_eq_zero_iff]
    exact Nat.pow_dvd_pow 2 (by omega)
  have h2t : 2 * t ≠ 0 := by
    intro h
    have hp : 2 ^ (k + 3) = 2 * 2 ^ (k + 2) := by
      rw [show k + 3 = (k + 2) + 1 by omega, pow_succ, mul_comm]
    have hcast : ((2 ^ (k + 3) : ℕ) : ZMod (2 ^ (k + 4))) = 0 := by
      rw [hp, Nat.cast_mul, Nat.cast_ofNat]
      exact h
    have hd := (ZMod.natCast_eq_zero_iff _ _).mp hcast
    exact (Nat.not_dvd_of_pos_of_lt (by positivity)
      (Nat.pow_lt_pow_right (by decide) (by omega : k + 3 < k + 4))) hd
  exact unitQuadraticGaussSum_eq_zero_of_square_zero _ t ht h2t a ha

theorem principalSquareSum_odd_prime_pow_eq_zero (p j : ℕ) [Fact p.Prime]
    (hp2 : p ≠ 2) (hj : 2 ≤ j) (a : ZMod (p ^ j)) (ha : IsUnit a) :
    principalSquareSum (p ^ j) a = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 2 := ⟨j - 2, by omega⟩
  rw [principalSquareSum_as_unitGauss,
    unitQuadraticGaussSum_odd_prime_pow p hp2 k (-a) ha.neg, mul_zero]

theorem principalSquareSum_two_pow_eq_zero (j : ℕ) (hj : 4 ≤ j)
    (a : ZMod (2 ^ j)) (ha : IsUnit a) : principalSquareSum (2 ^ j) a = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 4 := ⟨j - 4, by omega⟩
  rw [principalSquareSum_as_unitGauss,
    unitQuadraticGaussSum_two_pow_ge_four k (-a) ha.neg, mul_zero]

theorem norm_principalSquareSum_odd_prime_le (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (a : ZMod p) (ha : IsUnit a) :
    ‖principalSquareSum p a‖ ≤ 1 / (Real.sqrt p - 1) := by
  have hp : p.Prime := Fact.out
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hs := Real.sq_sqrt (Nat.cast_nonneg p)
  have hr := Real.sqrt_nonneg (p : ℝ)
  have hr1 : 1 < Real.sqrt (p : ℝ) := by nlinarith
  have hp1 : (0 : ℝ) < p - 1 := by linarith
  have hφ : (p.totient : ℝ) = (p : ℝ) - 1 := by
    rw [Nat.totient_prime hp, Nat.cast_sub hp.one_le, Nat.cast_one]
  rw [norm_principalSquareSum, hφ]
  calc
    _ ≤ (Real.sqrt p + 1) / ((p : ℝ) - 1) :=
      div_le_div_of_nonneg_right (norm_unitQuadraticGaussSum_prime_le p hp2 (-a) ha.neg) hp1.le
    _ = _ := by
      have hr0 : Real.sqrt (p : ℝ) - 1 ≠ 0 := by linarith
      have hp0 : (p : ℝ) - 1 ≠ 0 := hp1.ne'
      field_simp
      nlinarith

theorem scaled_norm_principalSquareSum_odd_prime_le (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (a : ZMod p) (ha : IsUnit a) :
    Real.sqrt p * ‖principalSquareSum p a‖ ≤ (1 - (Real.sqrt p)⁻¹)⁻¹ := by
  have hp : p.Prime := Fact.out
  have hs := Real.sq_sqrt (Nat.cast_nonneg p)
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hr := Real.sqrt_nonneg (p : ℝ)
  have hr1 : 1 < Real.sqrt (p : ℝ) := by nlinarith
  calc
    _ ≤ Real.sqrt p * (1 / (Real.sqrt p - 1)) :=
      mul_le_mul_of_nonneg_left (norm_principalSquareSum_odd_prime_le p hp2 a ha) hr
    _ = _ := by
      have hr0 : Real.sqrt (p : ℝ) ≠ 0 := by linarith
      have hrsub : Real.sqrt (p : ℝ) - 1 ≠ 0 := by linarith
      field_simp

theorem scaled_norm_principalSquareSum_two_pow_le (j : ℕ) (a : ZMod (2 ^ j))
    (ha : IsUnit a) : Real.sqrt (2 ^ j : ℕ) * ‖principalSquareSum (2 ^ j) a‖ ≤ 4 := by
  by_cases hj : 4 ≤ j
  · rw [principalSquareSum_two_pow_eq_zero j hj a ha, norm_zero, mul_zero]
    norm_num
  · have hj3 : j ≤ 3 := by omega
    have hq : ((2 ^ j : ℕ) : ℝ) ≤ 8 := by
      exact_mod_cast (Nat.pow_le_pow_right (by decide : 0 < 2) hj3)
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ (2 ^ j : ℕ) by positivity)
    have hr := Real.sqrt_nonneg ((2 ^ j : ℕ) : ℝ)
    have hroot : Real.sqrt (2 ^ j : ℕ) ≤ 4 := by nlinarith
    calc
      _ ≤ Real.sqrt (2 ^ j : ℕ) * 1 :=
        mul_le_mul_of_nonneg_left (norm_principalSquareSum_le_one _ a) hr
      _ ≤ _ := by simpa only [mul_one] using hroot

end PrimeSquares

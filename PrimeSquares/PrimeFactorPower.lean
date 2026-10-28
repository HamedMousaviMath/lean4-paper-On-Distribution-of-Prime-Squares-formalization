import PrimeSquares.PrimeFactorEstimates

/-! Elementary absorption of fixed prime-factor weights into q^epsilon. -/

open Finset

namespace PrimeSquares

theorem le_totient_mul_two_pow_primeFactors (q : ℕ) (_hq : 0 < q) :
    q ≤ q.totient * 2 ^ q.primeFactors.card := by
  have hprod : (∏ p ∈ q.primeFactors, p) ≤
      2 ^ q.primeFactors.card * ∏ p ∈ q.primeFactors, (p - 1) := by
    calc
      _ ≤ ∏ p ∈ q.primeFactors, 2 * (p - 1) := by
        apply prod_le_prod
        intro p hp
        have := (Nat.prime_of_mem_primeFactors hp).two_le
        omega
      _ = _ := by rw [prod_mul_distrib, prod_const]
  have hpos : 0 < ∏ p ∈ q.primeFactors, (p - 1) :=
    prod_pos fun p hp => by have := (Nat.prime_of_mem_primeFactors hp).two_le; omega
  apply le_of_mul_le_mul_right ?_ hpos
  calc
    q * ∏ p ∈ q.primeFactors, (p - 1) = q.totient * ∏ p ∈ q.primeFactors, p :=
      (Nat.totient_mul_prod_primeFactors q).symm
    _ ≤ q.totient * (2 ^ q.primeFactors.card * ∏ p ∈ q.primeFactors, (p - 1)) :=
      Nat.mul_le_mul_left _ hprod
    _ = _ := by ring

theorem primeFactor_pow_le_rpow (B : ℝ) (hB : 1 ≤ B) (ε : ℝ) (hε : 0 < ε) :
    ∃ A : ℝ, 0 < A ∧ ∀ q : ℕ, 0 < q →
      B ^ q.primeFactors.card ≤ A * (q : ℝ) ^ ε := by
  classical
  let N : ℕ := ⌈Real.exp (Real.log B / ε)⌉₊
  let A : ℝ := Real.exp ((N : ℝ) * Real.log B)
  refine ⟨A, Real.exp_pos _, ?_⟩
  intro q hq
  have hlogB : 0 ≤ Real.log B := Real.log_nonneg hB
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hcard : (q.primeFactors.filter (fun p => p ≤ N)).card ≤ N := by
    have hsub : q.primeFactors.filter (fun p => p ≤ N) ⊆ Icc 1 N := by
      intro p hp
      obtain ⟨hpq, hpN⟩ := mem_filter.mp hp
      exact mem_Icc.mpr ⟨(Nat.prime_of_mem_primeFactors hpq).one_le, hpN⟩
    simpa using card_le_card hsub
  have hlarge (p : ℕ) (hp : p.Prime) (hpN : N < p) : Real.log B ≤ ε * Real.log p := by
    have hNp : Real.exp (Real.log B / ε) ≤ (p : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast hpN.le)
    have hl := Real.log_le_log (Real.exp_pos _) hNp
    rw [Real.log_exp] at hl
    exact (div_le_iff₀ hε).mp hl |>.trans_eq (mul_comm _ _)
  have hsum : (q.primeFactors.card : ℝ) * Real.log B ≤
      (N : ℝ) * Real.log B + ε * Real.log q := by
    calc
      _ = ∑ p ∈ q.primeFactors, Real.log B := by simp
      _ ≤ ∑ p ∈ q.primeFactors,
          ((if p ≤ N then Real.log B else 0) + ε * Real.log (p : ℝ)) := by
        apply sum_le_sum
        intro p hp
        have hprime := Nat.prime_of_mem_primeFactors hp
        have hlp : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hprime.one_le)
        split_ifs with h
        · nlinarith
        · simpa only [zero_add] using hlarge p hprime (lt_of_not_ge h)
      _ = ((q.primeFactors.filter (fun p => p ≤ N)).card : ℝ) * Real.log B +
          ε * ∑ p ∈ q.primeFactors, Real.log (p : ℝ) := by
        rw [sum_add_distrib, ← sum_filter, ← mul_sum]
        simp
      _ ≤ _ := add_le_add
        (mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hlogB)
        (mul_le_mul_of_nonneg_left (primeFactors_log_budget q hq) hε.le)
  calc
    _ = Real.exp ((q.primeFactors.card : ℝ) * Real.log B) := by
      rw [← Real.log_pow, Real.exp_log (pow_pos (by linarith) _)]
    _ ≤ Real.exp ((N : ℝ) * Real.log B + ε * Real.log q) := Real.exp_le_exp.mpr hsum
    _ = _ := by
      rw [Real.exp_add, Real.rpow_def_of_pos hq0]
      exact congrArg (fun t : ℝ => A * Real.exp t) (mul_comm ε (Real.log q))

end PrimeSquares

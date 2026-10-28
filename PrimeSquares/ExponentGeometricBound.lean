import PrimeSquares.PrimeFactorPower

open Filter
namespace PrimeSquares

theorem exponent_add_one_le_geometric {r : ℝ} (hr : 1 < r) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ n : ℕ, (n : ℝ)+1 ≤ A*r^n := by
  have h := (isLittleO_coe_const_pow_of_one_lt (R := ℝ) hr).bound (by norm_num : (0 : ℝ) < 1)
  obtain ⟨n₀,hn₀⟩ := eventually_atTop.mp h
  refine ⟨(n₀ : ℝ)+2,by linarith [(Nat.cast_nonneg n₀ : (0 : ℝ) ≤ n₀)],?_⟩
  intro n
  have hp : 1 ≤ r^n := one_le_pow₀ hr.le
  by_cases hn : n₀ ≤ n
  · have hb : (n : ℝ) ≤ r^n := by
      simpa only [Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n),
        abs_of_nonneg (pow_nonneg (by linarith : 0 ≤ r) n),one_mul] using hn₀ n hn
    nlinarith [(Nat.cast_nonneg n₀ : (0 : ℝ) ≤ n₀)]
  · have hb : (n : ℝ)+1 ≤ n₀ := by exact_mod_cast (by omega : n+1 ≤ n₀)
    nlinarith [(Nat.cast_nonneg n₀ : (0 : ℝ) ≤ n₀)]

theorem rpow_nat_power_comm {x : ℝ} (hx : 0 ≤ x) (ε : ℝ) (n : ℕ) :
    (x^ε)^n = (x^n)^ε := by
  rw [←Real.rpow_natCast (x^ε) n,←Real.rpow_mul hx,
    ←Real.rpow_natCast x n,←Real.rpow_mul hx]
  congr 1
  ring

theorem primePower_exponent_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (p n : ℕ), 2 ≤ p →
      (n : ℝ)+1 ≤ A*((p : ℝ)^n)^ε := by
  obtain ⟨A,hA,ha⟩ := exponent_add_one_le_geometric
    (Real.one_lt_rpow (by norm_num : (1 : ℝ) < 2) hε)
  refine ⟨A,hA,?_⟩
  intro p n hp
  calc
    _ ≤ A*((2 : ℝ)^ε)^n := ha n
    _ = A*((2 : ℝ)^n)^ε := by rw [rpow_nat_power_comm (by norm_num)]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity)
        (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) (by exact_mod_cast hp : (2 : ℝ) ≤ p) n) hε.le)
      (by linarith)

end PrimeSquares

import PrimeSquares.DivisorProductGrowth

namespace PrimeSquares

theorem divisors_card_rpow_le_rpow {γ ε : ℝ} (hγ : 0 < γ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, 0 < q →
      (q.divisors.card : ℝ)^γ ≤ C*(q : ℝ)^ε := by
  obtain ⟨A,hA,ha⟩ := divisors_card_le_rpow (div_pos hε hγ)
  refine ⟨A^γ,Real.rpow_pos_of_pos hA _,?_⟩
  intro q hq
  have hqp : (0 : ℝ) < q := by exact_mod_cast hq
  calc
    _ ≤ (A*(q : ℝ)^(ε/γ))^γ :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) (ha q hq) hγ.le
    _ = A^γ*(q : ℝ)^((ε/γ)*γ) := by
      rw [Real.mul_rpow hA.le (Real.rpow_nonneg hqp.le _),←Real.rpow_mul hqp.le]
    _ = _ := by rw [div_mul_cancel₀ ε hγ.ne']

noncomputable def renDivisorConstant : ℝ :=
  Classical.choose (divisors_card_rpow_le_rpow (by norm_num : (0 : ℝ) < 3/2)
    (by norm_num : (0 : ℝ) < 1/12))

theorem renDivisorConstant_pos : 0 < renDivisorConstant :=
  (Classical.choose_spec (divisors_card_rpow_le_rpow (by norm_num : (0 : ℝ) < 3/2)
    (by norm_num : (0 : ℝ) < 1/12))).1

theorem ren_divisor_prefactor_bound (q : ℕ) (hq : 0 < q) :
    (q.divisors.card : ℝ)^(3/2 : ℝ) ≤ renDivisorConstant*(q : ℝ)^(1/12 : ℝ) :=
  (Classical.choose_spec (divisors_card_rpow_le_rpow (by norm_num : (0 : ℝ) < 3/2)
    (by norm_num : (0 : ℝ) < 1/12))).2 q hq

end PrimeSquares

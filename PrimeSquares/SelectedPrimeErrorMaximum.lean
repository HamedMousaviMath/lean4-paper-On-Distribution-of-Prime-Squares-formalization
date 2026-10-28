import PrimeSquares.Proposition419
import PrimeSquares.OperatorDecaySeries
import PrimeSquares.DyadicLogarithmicBudget
import PrimeSquares.OperatorMaximalNorm

/-!
# The actual selected error maximum over every valid dyadic scale

Invalid scales are set to zero. The error exponent A=2 in Proposition 4.19
gives summable operator norms, hence a genuine countable l2 maximum.
-/

open scoped lp
namespace PrimeSquares

noncomputable def selectedPrimeValidError {c : ℝ} (D : PagePrimeSquareDistributionInputs c)
    (δ Q : ℝ) (j : ℕ) : ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ) :=
  if Real.log Q ≤ δ * Real.sqrt (Real.log (((2 : ℕ)^j*2 : ℕ) : ℝ)) then
    selectedPrimeError D ((2 : ℕ)^j*2)
      (by have := dyadic_annular_scale_lower (M := 2) (by norm_num) j; omega) Q
  else 0

theorem selectedPrimeValidError_of_valid {c δ Q : ℝ} (D : PagePrimeSquareDistributionInputs c)
    (j : ℕ) (h : Real.log Q ≤ δ * Real.sqrt (Real.log (((2 : ℕ)^j*2 : ℕ) : ℝ))) :
    selectedPrimeValidError D δ Q j = selectedPrimeError D ((2 : ℕ)^j*2)
      (by have := dyadic_annular_scale_lower (M := 2) (by norm_num) j; omega) Q := by
  exact ite_eq_left h

theorem selectedPrimeError_countable_maximum {c δ : ℝ}
    (D : PagePrimeSquareDistributionInputs c) (H419 : Proposition419Bounds D δ) :
    ∃ K : ℝ, 0 < K ∧ ∀ Q : ℝ, 2 ≤ Q →
      ∀ f : ℓ²(ℤ, ℂ), ∃ E : ℓ²(ℤ, ℝ),
        (∀ j x, ‖selectedPrimeValidError D δ Q j f x‖ ≤ E x) ∧
        (∀ x, E x = ⨆ j : ℕ, ‖selectedPrimeValidError D δ Q j f x‖) ∧
        ‖E‖ ≤ K * Q^(-(1/2 : ℝ)) * ‖f‖ := by
  obtain ⟨C, hC, herr⟩ := H419.error 2 (by norm_num)
  let K := 2 * C * (Real.log 2)^(-(2 : ℝ))
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro Q hQ f
  let T := selectedPrimeValidError D δ Q
  let B := C * Q^(-(1/2 : ℝ)) * (Real.log 2)^(-(2 : ℝ))
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hdecay : ∀ j : ℕ, ‖T j‖ ≤ B * ((j : ℝ)+1)^(-(2 : ℝ)) := by
    intro j
    have hn : (2 : ℕ) ≤ (2 : ℕ)^j*2 := dyadic_annular_scale_lower (M := 2) (by norm_num) j
    by_cases hv : Real.log Q ≤ δ * Real.sqrt (Real.log (((2 : ℕ)^j*2 : ℕ) : ℝ))
    · have h := herr _ hn Q hQ hv
        (by have := dyadic_annular_scale_lower (M := 2) (by norm_num) j; omega)
      have hNmono : (((2 : ℕ)^j : ℕ) : ℝ) ≤ (((2 : ℕ)^j*2 : ℕ) : ℝ) := by
        exact_mod_cast (show (2 : ℕ)^j ≤ 2^j*2 by omega)
      have hlog : 1 + Real.log (((2 : ℕ)^j : ℕ) : ℝ) ≤
          1 + Real.log (((2 : ℕ)^j*2 : ℕ) : ℝ) :=
        add_le_add_right (Real.log_le_log (by positivity) hNmono) 1
      have hp : 0 < 1 + Real.log (((2 : ℕ)^j : ℕ) : ℝ) := by
        have h1 : (1 : ℝ) ≤ (((2 : ℕ)^j : ℕ) : ℝ) := by
          exact_mod_cast (one_le_pow₀ (by decide : 1 ≤ (2 : ℕ)) : 1 ≤ (2 : ℕ)^j)
        have := Real.log_nonneg h1
        linarith
      have hb := (Real.rpow_le_rpow_of_nonpos hp hlog (by norm_num : -(2 : ℝ) ≤ 0)).trans
        (dyadic_log_inverse_power (by norm_num : (0 : ℝ) ≤ 2) j)
      rw [show T j = selectedPrimeError D ((2 : ℕ)^j*2)
        (by have := dyadic_annular_scale_lower (M := 2) (by norm_num) j; omega) Q from
          selectedPrimeValidError_of_valid D j hv]
      exact h.trans (by
        dsimp [B]
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hb
          (show 0 ≤ C * Q^(-(1/2 : ℝ)) by positivity))
    · simp only [T, selectedPrimeValidError, ite_eq_right hv, norm_zero]
      positivity
  have hs : Summable (fun j : ℕ => ‖T j‖) := by
    simpa only [zero_add] using operator_norm_shift_summable hB (by norm_num : (2 : ℝ) ≤ 2)
      0 T (by simpa only [zero_add] using hdecay)
  have ht : (∑' j : ℕ, ‖T j‖) ≤ 2*B := by
    simpa only [zero_add, Nat.cast_zero, zero_add, Real.one_rpow, mul_one] using
      operator_norm_shift_tsum_bound hB (by norm_num : (2 : ℝ) ≤ 2) 0 T
        (by simpa only [zero_add] using hdecay)
  refine ⟨operatorMaximalL2 T hs f, ?_, (fun _ => rfl), ?_⟩
  · intro j x
    exact operatorMaximalValue_dominates T hs f j x
  · exact (operatorMaximalL2_norm_bound T hs f).trans (by
      have h := mul_le_mul_of_nonneg_right ht (norm_nonneg f)
      simpa only [K, B, mul_assoc, mul_comm, mul_left_comm] using h)

end PrimeSquares

import PrimeSquares.CircleApproximationData
import PrimeSquares.DyadicLogarithmicBudget

open scoped lp
namespace PrimeSquares

noncomputable def dyadicCircleErrorOperator (Q : ℝ)
    (χ : ℕ → ∀ r : ℚ, DirichletCharacter ℂ r.den)
    (κ : ℕ → ℚ → ℂ) (β : ℕ → ℝ) (j : ℕ) : ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ) :=
  circleMajorArcErrorOperator (sourceRationalCenters (sourceMajorArcScale (((2 : ℕ)^j : ℕ) : ℝ) Q))
    (2^j) (one_le_pow₀ (by decide : 1 ≤ (2 : ℕ))) (χ j) (κ j) (β j)

noncomputable def dyadicErrorConstant (A : ℝ) : ℝ :=
  2*(2 : ℝ)^A*(Real.log 2)^(-A)

theorem dyadicErrorConstant_pos (A : ℝ) : 0 < dyadicErrorConstant A := by
  have hl : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  dsimp [dyadicErrorConstant]
  positivity

theorem dyadicCircleError_operator_decay {P C B d c A : ℝ}
    (hP : 0 ≤ P) (hC : 0 ≤ C) (hB : 0 ≤ B) (hd : 0 ≤ d) (hc : 0 < c) (hA : 0 ≤ A) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ J : ℕ, N₀ ≤ (2 : ℕ)^J → ∀ Q : ℝ, 1 ≤ Q →
      Real.log Q ≤ (min (c/7) 1/8)*Real.sqrt (Real.log (((2 : ℕ)^J : ℕ) : ℝ)) →
    ∀ (χ : ℕ → ∀ r : ℚ, DirichletCharacter ℂ r.den)
      (κ : ℕ → ℚ → ℂ) (β : ℕ → ℝ),
      (∀ j : ℕ, J ≤ j → CircleAnalyticInputs (2^j) Q (χ j) (κ j) (β j) P C B d c) →
    ∀ j : ℕ, J ≤ j → ‖dyadicCircleErrorOperator Q χ κ β j‖ ≤
      dyadicErrorConstant A*Q^(-(1/2 : ℝ))*((j : ℝ)+1)^(-A) := by
  obtain ⟨N₀,hN₀,h⟩ := globalCircleApproximation_l2_operator hP hC hB hd hc hA
  refine ⟨N₀,hN₀,?_⟩
  intro J hJ Q hQ hQl χ κ β hi j hj
  have hp := two_pow_monotone hj
  have hN := hJ.trans hp
  have hstart : (1 : ℝ) ≤ (((2 : ℕ)^J : ℕ) : ℝ) := by
    exact_mod_cast (one_le_pow₀ (by decide : 1 ≤ (2 : ℕ)) : 1 ≤ (2 : ℕ)^J)
  have hqrange := sourceQRange_upward (N := (((2 : ℕ)^J : ℕ) : ℝ)) (M := (((2 : ℕ)^j : ℕ) : ℝ)) hc hstart (by exact_mod_cast hp) hQl
  have hm := h (2^j) hN Q hQ hqrange (χ j) (κ j) (β j) (hi j hj)
    (one_le_pow₀ (by decide : 1 ≤ (2 : ℕ)))
  have hl := dyadic_log_inverse_power hA j
  calc
    _ ≤ 2*((2 : ℝ)^A*Q^(-(1/2 : ℝ))*(1+Real.log (((2 : ℕ)^j : ℕ) : ℝ))^(-A)) := hm
    _ ≤ 2*((2 : ℝ)^A*Q^(-(1/2 : ℝ))*
        ((Real.log 2)^(-A)*((j : ℝ)+1)^(-A))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hl (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
          (Real.rpow_nonneg (by linarith : 0 ≤ Q) _))) (by norm_num)
    _ = _ := by dsimp [dyadicErrorConstant];ring

end PrimeSquares

import PrimeSquares.DyadicMaximalErrorPower

open scoped lp
namespace PrimeSquares

theorem dyadic_tail_power_log_bound {A : ℝ} (hA : 0 ≤ A) (J : ℕ) :
    ((J : ℝ)+1)^(1-(A+2)) ≤ (1+Real.log (((2 : ℕ)^J : ℕ) : ℝ))^(-A) := by
  have hJ : 1 ≤ (J : ℝ)+1 := by linarith [(Nat.cast_nonneg J : (0 : ℝ) ≤ J)]
  have hlp : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlu : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hlower : 0 < 1+Real.log (((2 : ℕ)^J : ℕ) : ℝ) := by
    rw [log_two_pow_nat]
    positivity
  have hbase : 1+Real.log (((2 : ℕ)^J : ℕ) : ℝ) ≤ (J : ℝ)+1 := by
    rw [log_two_pow_nat]
    nlinarith [(Nat.cast_nonneg J : (0 : ℝ) ≤ J)]
  exact (Real.rpow_le_rpow_of_exponent_le hJ (by linarith : 1-(A+2) ≤ -A)).trans
    (Real.rpow_le_rpow_of_nonpos hlower hbase (neg_nonpos.mpr hA))

noncomputable def maximalCircleErrorConstant (A : ℝ) : ℝ := 2*dyadicErrorConstant (A+2)

theorem maximalCircleErrorConstant_pos (A : ℝ) : 0 < maximalCircleErrorConstant A := by
  dsimp [maximalCircleErrorConstant]
  exact mul_pos (by norm_num) (dyadicErrorConstant_pos _)

theorem dyadicCircleError_maximal_log_rate {P C B d c A : ℝ}
    (hP : 0 ≤ P) (hC : 0 ≤ C) (hB : 0 ≤ B) (hd : 0 ≤ d) (hc : 0 < c) (hA : 0 ≤ A) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ J : ℕ, N₀ ≤ (2 : ℕ)^J → ∀ Q : ℝ, 1 ≤ Q →
      Real.log Q ≤ (min (c/7) 1/8)*Real.sqrt (Real.log (((2 : ℕ)^J : ℕ) : ℝ)) →
    ∀ (χ : ℕ → ∀ r : ℚ, DirichletCharacter ℂ r.den) (κ : ℕ → ℚ → ℂ) (β : ℕ → ℝ),
      (∀ j : ℕ, J ≤ j → CircleAnalyticInputs (2^j) Q (χ j) (κ j) (β j) P C B d c) →
    ∀ f : ℓ²(ℤ, ℂ), ∃ g : lp (fun _ : ℤ => ℝ) 2,
      (∀ x : ℤ, g x = ⨆ j : ℕ, ‖dyadicCircleErrorOperator Q χ κ β (J+j) f x‖) ∧
      ‖g‖ ≤ maximalCircleErrorConstant A*Q^(-(1/2 : ℝ))*
        (1+Real.log (((2 : ℕ)^J : ℕ) : ℝ))^(-A)*‖f‖ := by
  obtain ⟨N₀,hN₀,h⟩ := dyadicCircleError_maximal_power hP hC hB hd hc (by linarith : 2 ≤ A+2)
  refine ⟨N₀,hN₀,?_⟩
  intro J hJ Q hQ hQl χ κ β hi f
  obtain ⟨g,hg,hbound⟩ := h J hJ Q hQ hQl χ κ β hi f
  refine ⟨g,hg,hbound.trans ?_⟩
  have hk : 0 ≤ 2*(dyadicErrorConstant (A+2)*Q^(-(1/2 : ℝ))) := by
    have hpos := dyadicErrorConstant_pos (A+2)
    positivity
  calc
    _ ≤ 2*(dyadicErrorConstant (A+2)*Q^(-(1/2 : ℝ)))*
        (1+Real.log (((2 : ℕ)^J : ℕ) : ℝ))^(-A)*‖f‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (dyadic_tail_power_log_bound hA J) hk) (norm_nonneg f)
    _ = _ := by dsimp [maximalCircleErrorConstant];ring

end PrimeSquares

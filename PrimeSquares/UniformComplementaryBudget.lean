import PrimeSquares.ComplementaryMinorArcBound
import PrimeSquares.SourceLogPowerBudget

namespace PrimeSquares

theorem complementaryMinorBudget_uniform {C B d : ℝ}
    (hC : 0 ≤ C) (hB : 0 ≤ B) (hd : 0 ≤ d) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ Q : ℝ,
      complementaryMinorBudget N C B d (sourceMajorArcScale N Q) ≤
        (sourceMajorArcScale N Q)^(-(1/6 : ℝ)) := by
  obtain ⟨N₁,hN₁,hl⟩ := source_annular_log_power_uniform hd (by norm_num : (0 : ℝ) < 1/12)
  have he := eventually_two_rpow_budget (renSourceConstant_nonneg hC) (ghoshSourceConstant_nonneg hB)
    (by norm_num : -(1/3 : ℝ) < -(1/6 : ℝ)) (by norm_num : -(1/4 : ℝ) < -(1/6 : ℝ))
  obtain ⟨D,hD⟩ := Filter.eventually_atTop.mp he
  obtain ⟨N₂,hN₂⟩ := sourceMajorArcScale_uniform_lower D
  refine ⟨max N₁ N₂,by omega,?_⟩
  intro N hN Q
  have hn1 : N₁ ≤ N := (le_max_left _ _).trans hN
  have hn2 : N₂ ≤ N := (le_max_right _ _).trans hN
  have hR := sourceMajorArcScale_pos N Q
  have hlog := hl N hn1 Q
  have hp : renSourceConstant C*(Real.log ((N : ℝ)/2))^d*(sourceMajorArcScale N Q)^(-(5/12 : ℝ)) ≤
      renSourceConstant C*(sourceMajorArcScale N Q)^(-(1/3 : ℝ)) := by
    calc
      _ ≤ renSourceConstant C*(sourceMajorArcScale N Q)^(1/12 : ℝ)*
          (sourceMajorArcScale N Q)^(-(5/12 : ℝ)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlog (renSourceConstant_nonneg hC))
          (Real.rpow_nonneg hR.le _)
      _ = _ := by rw [mul_assoc,←Real.rpow_add hR];norm_num
  exact (add_le_add hp (le_refl (ghoshSourceConstant B*(sourceMajorArcScale N Q)^(-(1/4 : ℝ))))).trans
    (hD _ (hN₂ N hn2 Q))

theorem complementaryMinorBudget_uniform_log_rate {C B d A : ℝ}
    (hC : 0 ≤ C) (hB : 0 ≤ B) (hd : 0 ≤ d) (hA : 0 ≤ A) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ Q : ℝ, 1 ≤ Q →
      complementaryMinorBudget N C B d (sourceMajorArcScale N Q) ≤
        (2 : ℝ)^A*Q^(-(1/2 : ℝ))*(1+Real.log N)^(-A) := by
  obtain ⟨N₁,hN₁,hb⟩ := complementaryMinorBudget_uniform hC hB hd
  obtain ⟨N₂,hN₂⟩ := sourceMajorArcScale_logarithmic_rate hA
  refine ⟨max N₁ N₂,by omega,?_⟩
  intro N hN Q hQ
  exact (hb N ((le_max_left _ _).trans hN) Q).trans
    (hN₂ N ((le_max_right _ _).trans hN) Q hQ)

end PrimeSquares

import PrimeSquares.LogPowerAbsorption
import PrimeSquares.UniformMajorArcBudget

namespace PrimeSquares

theorem sourceMajorArcScale_log_lower (N Q : ℝ) :
    (Real.log N)^(1/10 : ℝ) ≤ Real.log (sourceMajorArcScale N Q) := by
  have h := Real.log_le_log (Real.exp_pos ((Real.log N)^(1/10 : ℝ)))
    (le_max_left (Real.exp ((Real.log N)^(1/10 : ℝ))) (Q^8))
  rwa [Real.log_exp] at h

theorem source_log_power_domination {N Q d : ℝ} (hN : 1 ≤ N) (hd : 0 ≤ d) :
    (Real.log N)^d ≤ (Real.log (sourceMajorArcScale N Q))^(10*d) := by
  have hL := Real.log_nonneg hN
  have hs := sourceMajorArcScale_log_lower N Q
  have hR : 0 ≤ Real.log (sourceMajorArcScale N Q) := (Real.rpow_nonneg hL _).trans hs
  have hp := Real.rpow_le_rpow (Real.rpow_nonneg hL _) hs (by norm_num : (0 : ℝ) ≤ 10)
  rw [←Real.rpow_mul hL] at hp
  norm_num at hp
  have h := Real.rpow_le_rpow hL hp hd
  rw [←Real.rpow_natCast (Real.log (sourceMajorArcScale N Q)) 10,←Real.rpow_mul hR] at h
  norm_num at h
  exact h

theorem source_annular_log_power_uniform {d ε : ℝ} (hd : 0 ≤ d) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ Q : ℝ,
      (Real.log ((N : ℝ)/2))^d ≤ (sourceMajorArcScale N Q)^ε := by
  obtain ⟨B,hB⟩ := Filter.eventually_atTop.mp (eventually_log_rpow_le_rpow (10*d) hε)
  obtain ⟨N₁,hN₁⟩ := sourceMajorArcScale_uniform_lower B
  refine ⟨max 2 N₁,by omega,?_⟩
  intro N hN Q
  have hn : (2 : ℝ) ≤ N := by exact_mod_cast (by omega : 2 ≤ N)
  have hlog : Real.log ((N : ℝ)/2) ≤ Real.log N :=
    Real.log_le_log (by linarith) (by linarith)
  calc
    _ ≤ (Real.log N)^d := Real.rpow_le_rpow (Real.log_nonneg (by linarith)) hlog hd
    _ ≤ (Real.log (sourceMajorArcScale N Q))^(10*d) := source_log_power_domination (by linarith) hd
    _ ≤ _ := hB _ (hN₁ N ((le_max_right _ _).trans hN) Q)

end PrimeSquares

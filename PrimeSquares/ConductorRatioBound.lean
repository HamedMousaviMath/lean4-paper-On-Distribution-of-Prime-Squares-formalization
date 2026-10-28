import PrimeSquares.ConductorDecay

namespace PrimeSquares

theorem conductorMajorant_linear_bound : ∃ T : ℝ,0 < T ∧
    ∀ q₀ : ℕ,0 < q₀ → conductorMajorant q₀ ≤ T*(q₀ : ℝ) := by
  obtain ⟨A,hA,h⟩ := primeFactor_pow_le_rpow 8 (by norm_num) (1/2) (by norm_num)
  refine ⟨64*A,by positivity,?_⟩
  intro q₀ hq₀
  calc
    _ ≤ 64*(A*(q₀ : ℝ)^(1/2 : ℝ))*Real.sqrt q₀ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (h q₀ hq₀) (by norm_num)) (Real.sqrt_nonneg _)
    _ = (64*A)*(Real.sqrt q₀*Real.sqrt q₀) := by rw [←Real.sqrt_eq_rpow];ring
    _ = _ := by rw [Real.mul_self_sqrt (Nat.cast_nonneg q₀)]

theorem conductorMajorant_ratio_uniform : ∃ T : ℝ,0 < T ∧
    ∀ q₀ : ℕ,0 < q₀ → conductorMajorant q₀/(q₀ : ℝ) ≤ T := by
  obtain ⟨T,hT,h⟩ := conductorMajorant_linear_bound
  refine ⟨T,hT,?_⟩
  intro q₀ hq₀
  exact (div_le_iff₀ (by exact_mod_cast hq₀ : (0 : ℝ) < q₀)).mpr (h q₀ hq₀)

end PrimeSquares

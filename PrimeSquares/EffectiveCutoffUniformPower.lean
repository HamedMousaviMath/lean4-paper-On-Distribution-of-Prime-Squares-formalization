import PrimeSquares.EffectiveCutoffPower
namespace PrimeSquares
theorem effectiveCollarCutoff_power_bound {Q T η : ℝ} (hQ : 0 < Q) (hη : 0 ≤ η)
    {q₀ : ℕ} (hq₀ : 0 < q₀) (hT : conductorMajorant q₀/(q₀ : ℝ) ≤ T) :
    (effectiveCollarCutoff Q q₀)^(-η) ≤ Q^(-η)*T^η := by
  have hB : 0 ≤ conductorMajorant q₀ := le_trans (by norm_num) (conductorMajorant_one_le q₀ hq₀)
  rw [effectiveCollarCutoff_rpow hQ hq₀]
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_pos_of_pos hQ _).le
  exact Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ conductorMajorant q₀/(q₀ : ℝ)) hT hη
end PrimeSquares

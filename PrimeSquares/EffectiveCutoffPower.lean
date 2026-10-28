import PrimeSquares.CollarConstantLinearity
namespace PrimeSquares
theorem effectiveCollarCutoff_rpow {Q : ℝ} (hQ : 0 < Q) {q₀ : ℕ} (hq₀ : 0 < q₀) (η : ℝ) :
    (effectiveCollarCutoff Q q₀)^(-η)=Q^(-η)*(conductorMajorant q₀/(q₀ : ℝ))^η := by
  have hq : (0 : ℝ) < q₀ := by exact_mod_cast hq₀
  have hB : 0 < conductorMajorant q₀ := lt_of_lt_of_le (by norm_num) (conductorMajorant_one_le q₀ hq₀)
  unfold effectiveCollarCutoff
  rw [Real.div_rpow (mul_nonneg hQ.le hq.le) hB.le,Real.mul_rpow hQ.le hq.le,
    Real.div_rpow hB.le hq.le,Real.rpow_neg hq.le,Real.rpow_neg hB.le]
  field_simp
end PrimeSquares

import PrimeSquares.PhysicalLowKernel

namespace PrimeSquares

noncomputable def physicalLowAmplitude (N Q : ℕ) : ℝ :=
  lowSpatialConstant*(Q : ℝ)*Real.log (2*(Q : ℝ))/(N : ℝ)^2

theorem physicalLowAmplitude_nonneg (N Q : ℕ) (hQ : 1 ≤ Q) : 0 ≤ physicalLowAmplitude N Q := by
  have hQr : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  unfold physicalLowAmplitude
  exact div_nonneg (mul_nonneg (mul_nonneg lowSpatialConstant_nonneg (Nat.cast_nonneg _))
    (Real.log_nonneg (by linarith))) (sq_nonneg _)

theorem physicalLowAmplitude_mono {N M Q : ℕ} (hN : 1 ≤ N) (hNM : N ≤ M) (hQ : 1 ≤ Q) :
    physicalLowAmplitude M Q ≤ physicalLowAmplitude N Q := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hNr : (N : ℝ) ≤ M := by exact_mod_cast hNM
  have hQr : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  unfold physicalLowAmplitude
  exact div_le_div_of_nonneg_left
    (mul_nonneg (mul_nonneg lowSpatialConstant_nonneg (Nat.cast_nonneg _)) (Real.log_nonneg (by linarith)))
    (sq_pos_of_pos hNp) (pow_le_pow_left₀ hNp.le hNr 2)

end PrimeSquares

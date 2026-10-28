import PrimeSquares.LocalPrimeScalarBalance

/-! # A uniform large-scale threshold for the balanced splitting parameter -/

namespace PrimeSquares

noncomputable def primeStoppingStart (δ Q : ℝ) : ℝ :=
  Real.exp ((2+Real.log Q/δ)^2)

theorem primeStoppingStart_bounds {δ B : ℝ} (hδ : 0 < δ) (hB : 0 < B) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ L Q : ℝ, 2 ≤ L → 2 ≤ Q → Real.log Q ≤ B*L →
      2 ≤ primeStoppingStart δ Q ∧
      Real.log Q ≤ δ*Real.sqrt (Real.log (primeStoppingStart δ Q)) ∧
      Real.log (primeStoppingStart δ Q) ≤ C₀*L^2 := by
  let C₀ := (2+B/δ)^2
  have hb : 0 < 2+B/δ := by positivity
  refine ⟨C₀, sq_pos_of_pos hb, ?_⟩
  intro L Q hL hQ hlog
  have hQ0 : 0 < Q := by linarith
  have hlog0 : 0 < Real.log Q := Real.log_pos (by linarith)
  have hx : 0 < 2+Real.log Q/δ := by positivity
  have hx2 : 2 ≤ 2+Real.log Q/δ := by have := div_nonneg hlog0.le hδ.le; linarith
  have hlogN : Real.log (primeStoppingStart δ Q) = (2+Real.log Q/δ)^2 := Real.log_exp _
  have hroot : Real.sqrt (Real.log (primeStoppingStart δ Q)) = 2+Real.log Q/δ := by
    rw [hlogN, Real.sqrt_sq hx.le]
  refine ⟨?_, ?_, ?_⟩
  · have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    exact (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 2)).mp (by nlinarith)
  · rw [hroot]
    have he : δ*(2+Real.log Q/δ)=2*δ+Real.log Q := by field_simp
    rw [he]
    linarith
  · rw [hlogN]
    have hd : Real.log Q/δ ≤ (B/δ)*L := by
      simpa only [div_mul_eq_mul_div] using div_le_div_of_nonneg_right hlog hδ.le
    have hbase : 2+Real.log Q/δ ≤ (2+B/δ)*L := by nlinarith
    have hs := pow_le_pow_left₀ hx.le hbase 2
    simpa only [mul_pow, C₀] using hs

end PrimeSquares

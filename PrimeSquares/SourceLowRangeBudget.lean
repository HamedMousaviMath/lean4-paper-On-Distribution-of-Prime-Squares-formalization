import PrimeSquares.SourceLowFamilies

namespace PrimeSquares

theorem radius_le_square {R : ℝ} (hR : 1 ≤ R) : R ≤ R^2 := by
  nlinarith [mul_nonneg (by linarith : 0 ≤ R) (by linarith : 0 ≤ R-1)]

theorem source_squared_low_width {N Q R : ℝ} (hQ : 1 ≤ Q) (hQR : Q ≤ R)
    (hb : 2*R^8 ≤ N^2) : 2*Q ≤ N^2 := by
  have hR : 1 ≤ R := hQ.trans hQR
  apply source_low_width_budget hQ (hQR.trans (radius_le_square hR))
  convert hb using 1
  ring

theorem source_exceptional_squared_radius {q₀ : ℕ} (hq₀ : 0 < q₀) {Q R : ℝ}
    (hQ : 0 ≤ Q) (hQR : Q ≤ R) (hqR : (q₀ : ℝ) ≤ R) :
    Q*(q₀ : ℝ)/conductorMajorant q₀ ≤ R^2 := by
  have hR : 0 ≤ R := hQ.trans hQR
  have hB1 := conductorMajorant_one_le q₀ hq₀
  have hB : 0 < conductorMajorant q₀ := lt_of_lt_of_le (by norm_num) hB1
  apply (div_le_iff₀ hB).mpr
  calc
    _ ≤ R*R := mul_le_mul hQR hqR (Nat.cast_nonneg _) hR
    _ = R^2 := by ring
    _ ≤ R^2*conductorMajorant q₀ := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hB1 (sq_nonneg R)

theorem source_fourth_budget_to_eighth {N R : ℝ} (h : R^4 ≤ N/2) : 2*R^8 ≤ N^2 := by
  have hh : 2*R^4 ≤ N := by linarith
  have hs := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 2*R^4) hh 2
  nlinarith [sq_nonneg (R^4)]

end PrimeSquares
